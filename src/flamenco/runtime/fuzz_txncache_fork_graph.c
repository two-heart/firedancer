#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#if !FD_HAS_ATOMIC
#error "This target requires FD_HAS_ATOMIC"
#endif

#include <stdlib.h>
#include <string.h>

#include "../../util/fd_util.h"
#include "fd_txncache.h"
#include "fd_txncache_private.h"

/* fuzz_txncache_fork_graph is a stateful differential fuzzer for the
   fork-aware transaction cache (fd_txncache).  It drives the real
   structure and an independent reference model through the same
   sequence of operations and, after every operation, asserts that

     (a) every query answer matches the model oracle exactly, and
     (b) the real structure's internal bookkeeping (page ownership,
         pool accounting, frozen state, and the parent/child/sibling
         fork tree) is self-consistent and matches the model.

   The input byte stream is the program: each byte (after a short
   prologue choosing the cache geometry) selects and parameterizes one
   operation.  When the input is exhausted the program ends -- there is
   no PRNG fallback, so every consumed byte maps to behavior and growing
   the input grows the program.  This keeps coverage-guided mutation
   effective for reaching deep states.

   Fork lifecycle mirrors production frozen states:

     NEW    (0)  attach_child: live, no blockhash yet
     HASHED (1)  attach_blockhash: has a blockhash, usable as an insert
                 block context, but not queryable and not rootable
     FINAL  (2)  finalize_fork: has a blockhash + txnhash offset, usable
                 as a query/insert block context, parent, and root

   A fork acquires its blockhash via exactly one of attach_blockhash or
   finalize_fork (never both) so its (blockhash, offset) pair never
   mutates after assignment -- matching the realistic contract and
   keeping the model oracle exact.

   The op_extend_root macro (attach a child off the root, finalize it,
   advance the root onto it) lets a run of one byte value build a deep
   root chain cheaply, so the blockhash-distance root eviction path
   (root_cnt > FD_TXNCACHE_MAX_BLOCKHASH_DISTANCE, the steady-state
   common case in production) is reachable under mutation.

   Known coverage gap: filling a single blockhash to its page capacity
   requires >=FD_TXNCACHE_TXNS_PER_PAGE (16384) inserts referencing one
   blockhash, so the multi-page txnpage allocation and purge_stale
   compaction paths are not exercised here -- reaching them needs
   programs far larger than is practical for this differential harness. */

#define FUZZ_MAX_LIVE_SLOTS    (4UL)
#define FUZZ_MAX_TXN_PER_SLOT  (256UL)
#define FUZZ_MAX_ACTIVE_SLOTS  (FD_TXNCACHE_MAX_BLOCKHASH_DISTANCE+FUZZ_MAX_LIVE_SLOTS)
#define FUZZ_MAX_ACTIONS       (2048UL)
#define FUZZ_MAX_MODEL_TXNS    (768UL)
#define FUZZ_ROOT_HISTORY_MAX  (FD_TXNCACHE_MAX_BLOCKHASH_DISTANCE+FUZZ_MAX_ACTIONS+4UL)

#define NULL_FORK ((fd_txncache_fork_id_t){ .val = USHORT_MAX })

/* Fork frozen states (mirror fd_txncache.c). */
#define FORK_NEW    (0)
#define FORK_HASHED (1)
#define FORK_FINAL  (2)

/* Mirror fd_txncache.c's private local layout so this test target can
   assert cheap structural invariants without exporting production API. */
typedef struct fuzz_blockcache_private {
  fd_txncache_blockcache_shmem_t * shmem;
  uint *                           heads;
  ushort *                         pages;
  descends_set_t *                 descends;
} fuzz_blockcache_private_t;

struct fd_txncache_private {
  fd_txncache_shmem_t *            shmem;
  fd_txncache_blockcache_shmem_t * blockcache_shmem_pool;
  fuzz_blockcache_private_t *      blockcache_pool;
  blockhash_map_t *                blockhash_map;
  ushort *                         txnpages_free;
  fd_txncache_txnpage_t *          txnpages;
  ushort *                         scratch_pages;
  uint *                           scratch_heads;
  fd_txncache_txnpage_t *          scratch_txnpage;
};

typedef struct {
  uchar const * cur;
  ulong         rem;
} fuzz_cursor_t;

typedef struct {
  int       alive;
  int       frozen;     /* FORK_NEW / FORK_HASHED / FORK_FINAL */
  ushort    parent;
  uint      generation;
  ulong     txnhash_offset;
  fd_hash_t blockhash;
} model_fork_t;

typedef struct {
  int       used;
  ushort    block_fork;
  ushort    txn_fork;
  uint      generation;
  fd_hash_t txnhash;
} model_txn_t;

typedef struct {
  fd_txncache_t * tc;
  ulong           max_live_slots;

  model_fork_t fork[ FUZZ_MAX_ACTIVE_SLOTS ];
  model_txn_t  txn [ FUZZ_MAX_MODEL_TXNS   ];
  ulong        txn_cnt;
  ulong        live_cnt;
  ulong        hash_nonce;

  ushort current_root;
  ushort roots[ FUZZ_ROOT_HISTORY_MAX ];
  ulong  roots_head;
  ulong  roots_tail;
  ulong  root_cnt;
} model_t;

static uchar * fuzz_shmem;
static uchar * fuzz_ljoin;
static ulong   fuzz_shmem_fp;
static ulong   fuzz_ljoin_fp;
static model_t fuzz_model[ 1 ];

static void
hash_from_seed( fd_hash_t * h,
                ulong       tag,
                ulong       a,
                ulong       b ) {
  ulong seed = fd_ulong_hash( tag ^ (0x9e3779b97f4a7c15UL*a) ^ fd_ulong_bswap( b+1UL ) );
  h->ul[ 0 ] = 0x243f6a8885a308d3UL ^ seed;
  h->ul[ 1 ] = 0x13198a2e03707344UL ^ fd_ulong_hash( seed + a );
  h->ul[ 2 ] = 0xa4093822299f31d0UL ^ fd_ulong_hash( seed + b );
  h->ul[ 3 ] = 0x082efa98ec4e6c89UL ^ fd_ulong_hash( seed + tag + a + b );
}

/* fuzz_u8 returns the next input byte, or 0 once the input is exhausted.
   The caller (the action loop) stops issuing operations when the input
   runs out, so the program length is determined entirely by the input;
   there is no PRNG fallback that would decouple bytes from behavior. */

static uchar
fuzz_u8( fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( !cur->rem ) ) return 0U;
  uchar v = cur->cur[ 0 ];
  cur->cur++;
  cur->rem--;
  return v;
}

static ulong
fuzz_bounded( fuzz_cursor_t * cur,
              ulong           bound ) {
  if( FD_UNLIKELY( bound<=1UL ) ) return 0UL;

  ulong x = 0UL;
  for( ulong shift=0UL, max=bound-1UL; max; shift+=8UL, max>>=8UL )
    x |= (ulong)fuzz_u8( cur ) << shift;
  return x % bound;
}

static fd_txncache_t *
setup( ulong max_live_slots, ulong max_txn_per_slot ) {
  fd_txncache_shmem_t * shtc = fd_txncache_shmem_join( fd_txncache_shmem_new( fuzz_shmem, max_live_slots, max_txn_per_slot ) );
  FD_TEST( shtc );

  fd_txncache_t * tc = fd_txncache_join( fd_txncache_new( fuzz_ljoin, shtc ) );
  FD_TEST( tc );
  return tc;
}

static int
model_descends( model_t const * m,
                ushort          child,
                ushort          ancestor ) {
  if( FD_UNLIKELY( child>=FUZZ_MAX_ACTIVE_SLOTS || ancestor>=FUZZ_MAX_ACTIVE_SLOTS ) ) return 0;

  for( ushort cur=child; cur!=USHORT_MAX; ) {
    if( FD_UNLIKELY( !m->fork[ cur ].alive ) ) return 0;
    ushort parent = m->fork[ cur ].parent;
    if( parent==ancestor ) return 1;
    cur = parent;
  }
  return 0;
}

static int
model_in_current_tree( model_t const * m,
                       ushort          fork_id ) {
  return fork_id==m->current_root || model_descends( m, fork_id, m->current_root );
}

static ulong
model_current_tree_cnt( model_t const * m ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ )
    if( m->fork[ i ].alive && model_in_current_tree( m, (ushort)i ) ) cnt++;
  return cnt;
}

/* model_pick_fork selects a uniformly-random alive fork (using cursor
   bytes) that is in the current tree (if want_current_tree) and whose
   frozen state is in [frozen_lo,frozen_hi].  Returns USHORT_MAX if no
   fork qualifies. */

static ushort
model_pick_fork( model_t const * m,
                 fuzz_cursor_t * cur,
                 int             want_current_tree,
                 int             frozen_lo,
                 int             frozen_hi ) {
  ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
  ulong  candidate_cnt = 0UL;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !m->fork[ i ].alive ) ) continue;
    if( m->fork[ i ].frozen<frozen_lo || m->fork[ i ].frozen>frozen_hi ) continue;
    if( want_current_tree && !model_in_current_tree( m, (ushort)i ) ) continue;
    candidate[ candidate_cnt++ ] = (ushort)i;
  }

  if( FD_UNLIKELY( !candidate_cnt ) ) return USHORT_MAX;
  return candidate[ fuzz_bounded( cur, candidate_cnt ) ];
}

/* model_pick_strict_ancestor returns a random strict ancestor of
   fork_id that carries a usable blockhash.  For a query context
   (want_final) only FINAL ancestors qualify; for an insert context any
   ancestor with a blockhash (HASHED or FINAL) qualifies. */

static ushort
model_pick_strict_ancestor( model_t const * m,
                            fuzz_cursor_t * cur,
                            ushort          fork_id,
                            int             want_final ) {
  ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
  ulong  candidate_cnt = 0UL;

  for( ushort cur_id=m->fork[ fork_id ].parent; cur_id!=USHORT_MAX; cur_id=m->fork[ cur_id ].parent ) {
    if( FD_UNLIKELY( !m->fork[ cur_id ].alive ) ) break;
    int ok = want_final ? (m->fork[ cur_id ].frozen==FORK_FINAL) : (m->fork[ cur_id ].frozen>=FORK_HASHED);
    if( ok ) candidate[ candidate_cnt++ ] = cur_id;
  }

  if( FD_UNLIKELY( !candidate_cnt ) ) return USHORT_MAX;
  return candidate[ fuzz_bounded( cur, candidate_cnt ) ];
}

/* model_hash_on_strict_ancestry returns 1 if any strict ancestor of
   fork_id that carries a blockhash (HASHED or FINAL) holds blockhash. */

static int
model_hash_on_strict_ancestry( model_t const *   m,
                               ushort            fork_id,
                               fd_hash_t const * blockhash ) {
  for( ushort cur_id=m->fork[ fork_id ].parent; cur_id!=USHORT_MAX; cur_id=m->fork[ cur_id ].parent ) {
    if( FD_UNLIKELY( !m->fork[ cur_id ].alive ) ) break;
    if( m->fork[ cur_id ].frozen>=FORK_HASHED && fd_hash_eq( &m->fork[ cur_id ].blockhash, blockhash ) ) return 1;
  }
  return 0;
}

/* model_make_fresh_hash produces a blockhash that does not collide with
   any blockhash already present on fork_id's strict ancestry, so that
   blockhash_on_fork resolves unambiguously along that chain. */

static void
model_make_fresh_hash( model_t *   m,
                       ushort      fork_id,
                       fd_hash_t * blockhash ) {
  do {
    hash_from_seed( blockhash, 0xB10C000000000000UL, ++m->hash_nonce, fork_id );
  } while( model_hash_on_strict_ancestry( m, fork_id, blockhash ) );
}

/* model_make_finalize_hash usually mints a fresh unique blockhash but,
   one time in four, reuses a blockhash from an unrelated fork to stress
   duplicate-blockhash handling (multiple entries in one map bucket,
   disambiguated by the descends set).  The reused hash is never one on
   fork_id's own strict ancestry. */

static void
model_make_finalize_hash( model_t *       m,
                          fuzz_cursor_t * cur,
                          ushort          fork_id,
                          fd_hash_t *     blockhash ) {
  int duplicate = !(fuzz_u8( cur ) & 3U);
  if( duplicate ) {
    ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
    ulong  candidate_cnt = 0UL;
    for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
      if( FD_UNLIKELY( !m->fork[ i ].alive ) ) continue;
      if( FD_UNLIKELY( m->fork[ i ].frozen<FORK_HASHED ) ) continue;
      if( FD_UNLIKELY( i==fork_id || model_descends( m, fork_id, (ushort)i ) ) ) continue;
      candidate[ candidate_cnt++ ] = (ushort)i;
    }
    if( candidate_cnt ) {
      ushort src = candidate[ fuzz_bounded( cur, candidate_cnt ) ];
      if( !model_hash_on_strict_ancestry( m, fork_id, &m->fork[ src ].blockhash ) ) {
        *blockhash = m->fork[ src ].blockhash;
        return;
      }
    }
  }

  model_make_fresh_hash( m, fork_id, blockhash );
}

static void
model_add_fork( model_t *             m,
                fd_txncache_fork_id_t fork_id,
                ushort                parent,
                uint                  generation ) {
  FD_TEST( fork_id.val<FUZZ_MAX_ACTIVE_SLOTS );
  model_fork_t * fork = &m->fork[ fork_id.val ];
  memset( fork, 0, sizeof(*fork) );
  fork->alive      = 1;
  fork->frozen     = FORK_NEW;
  fork->parent     = parent;
  fork->generation = generation;
  m->live_cnt++;
}

static void
model_remove_only( model_t * m,
                   ushort    fork_id ) {
  if( FD_UNLIKELY( fork_id>=FUZZ_MAX_ACTIVE_SLOTS || !m->fork[ fork_id ].alive ) ) return;
  m->fork[ fork_id ].alive = 0;
  m->live_cnt--;
}

static void
model_remove_subtree( model_t * m,
                      ushort    fork_id ) {
  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( m->fork[ i ].alive && m->fork[ i ].parent==fork_id )
      model_remove_subtree( m, (ushort)i );
  }
  model_remove_only( m, fork_id );
}

static void
model_init( model_t *       m,
            fd_txncache_t * tc,
            ulong           max_live_slots ) {
  memset( m, 0, sizeof(*m) );
  m->tc             = tc;
  m->max_live_slots = max_live_slots;
  m->current_root   = USHORT_MAX;

  fd_txncache_fork_id_t root = fd_txncache_attach_child( tc, NULL_FORK );
  model_add_fork( m, root, USHORT_MAX, tc->blockcache_pool[ root.val ].shmem->generation );

  fd_hash_t blockhash[ 1 ];
  hash_from_seed( blockhash, 0xB10C000000000000UL, 0UL, 0UL );
  fd_txncache_finalize_fork( tc, root, 0UL, blockhash->uc );

  m->fork[ root.val ].frozen          = FORK_FINAL;
  m->fork[ root.val ].blockhash       = *blockhash;
  m->fork[ root.val ].txnhash_offset  = 0UL;
  m->current_root                     = root.val;
  m->roots[ m->roots_tail++ ]         = root.val;
}

static int
model_query( model_t const *   m,
             ushort            fork_id,
             ushort            block_fork,
             fd_hash_t const * txnhash ) {
  model_fork_t const * block = &m->fork[ block_fork ];
  ulong off = block->txnhash_offset;

  for( ulong i=0UL; i<m->txn_cnt; i++ ) {
    model_txn_t const * txn = &m->txn[ i ];
    if( FD_UNLIKELY( !txn->used ) ) continue;
    if( txn->block_fork!=block_fork ) continue;
    if( FD_UNLIKELY( txn->txn_fork>=FUZZ_MAX_ACTIVE_SLOTS ) ) continue;

    model_fork_t const * txn_fork = &m->fork[ txn->txn_fork ];
    if( FD_UNLIKELY( !txn_fork->alive ) ) continue;
    if( FD_UNLIKELY( txn_fork->generation!=txn->generation ) ) continue;
    if( !(txn->txn_fork==fork_id || model_descends( m, fork_id, txn->txn_fork )) ) continue;

    if( !memcmp( txnhash->uc+off, txn->txnhash.uc+off, 20UL ) ) return 1;
  }

  return 0;
}

/* check_cache_invariants verifies the real structure's internal
   bookkeeping against the model.  It is O(active_slots + max_txnpages),
   so it is cheap to run after every operation even at the maximum fork
   tree depth. */

static void
check_cache_invariants( model_t const * m ) {
  fd_txncache_t * tc = m->tc;
  FD_TEST( tc->shmem->txnpages_free_cnt<=tc->shmem->max_txnpages );
  FD_TEST( tc->shmem->max_txnpages<=512U );

  ulong pool_free = blockcache_pool_free( tc->blockcache_shmem_pool );
  FD_TEST( pool_free + m->live_cnt == blockcache_pool_max( tc->blockcache_shmem_pool ) );

  /* Page ownership: every txnpage is owned by exactly one live fork or
     is on the free list, and all pages are accounted for. */
  uchar page_seen[ 512 ];
  memset( page_seen, 0, sizeof(page_seen) );
  ulong used_pages = 0UL;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !m->fork[ i ].alive ) ) continue;

    fuzz_blockcache_private_t const * bc = &tc->blockcache_pool[ i ];
    FD_TEST( bc->shmem->generation==m->fork[ i ].generation );
    FD_TEST( bc->shmem->pages_cnt<=tc->shmem->txnpages_per_blockhash_max );
    FD_TEST( bc->shmem->frozen==m->fork[ i ].frozen );

    for( ulong j=0UL; j<bc->shmem->pages_cnt; j++ ) {
      ushort page = bc->pages[ j ];
      FD_TEST( page<tc->shmem->max_txnpages );
      FD_TEST( !page_seen[ page ] );
      page_seen[ page ] = 1U;
      used_pages++;
    }
    for( ulong j=bc->shmem->pages_cnt; j<tc->shmem->txnpages_per_blockhash_max; j++ ) {
      FD_TEST( bc->pages[ j ]==USHORT_MAX );
    }
  }

  for( ulong i=0UL; i<tc->shmem->txnpages_free_cnt; i++ ) {
    ushort page = tc->txnpages_free[ i ];
    FD_TEST( page<tc->shmem->max_txnpages );
    FD_TEST( !page_seen[ page ] );
    page_seen[ page ] = 1U;
  }

  FD_TEST( used_pages + tc->shmem->txnpages_free_cnt == tc->shmem->max_txnpages );

  /* Fork tree: the real child/sibling linked lists for the current tree
     must exactly enumerate the model's children, with no cycles, no
     duplicates, and correct parentage.  Forks outside the current tree
     (old roots pending eviction) may have stale links and are not
     checked.  Compute current-tree membership in O(active_slots) via a
     breadth-first sweep over the model's parent relation. */
  ushort child_head[ FUZZ_MAX_ACTIVE_SLOTS ];
  ushort child_sib [ FUZZ_MAX_ACTIVE_SLOTS ];
  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) child_head[ i ] = USHORT_MAX;
  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( !m->fork[ i ].alive ) continue;
    ushort parent = m->fork[ i ].parent;
    if( parent<FUZZ_MAX_ACTIVE_SLOTS ) {
      child_sib[ i ]       = child_head[ parent ];
      child_head[ parent ] = (ushort)i;
    }
  }

  uchar  in_tree[ FUZZ_MAX_ACTIVE_SLOTS ];
  ushort queue  [ FUZZ_MAX_ACTIVE_SLOTS ];
  memset( in_tree, 0, sizeof(in_tree) );
  ulong qhead = 0UL, qtail = 0UL;
  if( m->current_root<FUZZ_MAX_ACTIVE_SLOTS && m->fork[ m->current_root ].alive ) {
    in_tree[ m->current_root ] = 1U;
    queue[ qtail++ ] = m->current_root;
  }
  while( qhead<qtail ) {
    ushort p = queue[ qhead++ ];
    for( ushort c=child_head[ p ]; c!=USHORT_MAX; c=child_sib[ c ] ) {
      if( !in_tree[ c ] ) { in_tree[ c ] = 1U; queue[ qtail++ ] = c; }
    }
  }

  uchar reached[ FUZZ_MAX_ACTIVE_SLOTS ];
  memset( reached, 0, sizeof(reached) );
  for( ulong parent_id=0UL; parent_id<FUZZ_MAX_ACTIVE_SLOTS; parent_id++ ) {
    if( !in_tree[ parent_id ] ) continue;

    ushort child_id = tc->blockcache_pool[ parent_id ].shmem->child_id.val;
    for( ulong depth=0UL; child_id!=USHORT_MAX; depth++ ) {
      FD_TEST( depth<FUZZ_MAX_ACTIVE_SLOTS );
      FD_TEST( child_id<FUZZ_MAX_ACTIVE_SLOTS );
      fuzz_blockcache_private_t const * child = &tc->blockcache_pool[ child_id ];
      FD_TEST( m->fork[ child_id ].alive );
      FD_TEST( child->shmem->frozen>=0 );
      FD_TEST( m->fork[ child_id ].parent==(ushort)parent_id );
      FD_TEST( !reached[ child_id ] );
      reached[ child_id ] = 1U;
      child_id = child->shmem->sibling_id.val;
    }
  }

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( in_tree[ i ] && (ushort)i!=m->current_root ) FD_TEST( reached[ i ] );
  }
}

static void
op_attach( model_t *       m,
           fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( model_current_tree_cnt( m )>=m->max_live_slots ) ) return;
  if( FD_UNLIKELY( !blockcache_pool_free( m->tc->blockcache_shmem_pool ) ) ) return;

  /* Build off a fork that already carries a blockhash (HASHED or FINAL)
     so descendants have a usable insert/query block context. */
  ushort parent = model_pick_fork( m, cur, 1, FORK_HASHED, FORK_FINAL );
  if( FD_UNLIKELY( parent==USHORT_MAX ) ) return;

  fd_txncache_fork_id_t child = fd_txncache_attach_child( m->tc, (fd_txncache_fork_id_t){ .val = parent } );
  model_add_fork( m, child, parent, m->tc->blockcache_pool[ child.val ].shmem->generation );
}

static void
op_attach_blockhash( model_t *       m,
                     fuzz_cursor_t * cur ) {
  ushort fork_id = model_pick_fork( m, cur, 1, FORK_NEW, FORK_NEW );
  if( FD_UNLIKELY( fork_id==USHORT_MAX ) ) return;

  fd_hash_t blockhash[ 1 ];
  model_make_fresh_hash( m, fork_id, blockhash );

  fd_txncache_attach_blockhash( m->tc, (fd_txncache_fork_id_t){ .val = fork_id }, blockhash->uc );
  m->fork[ fork_id ].frozen         = FORK_HASHED;
  m->fork[ fork_id ].blockhash      = *blockhash;
  m->fork[ fork_id ].txnhash_offset = 0UL;
}

static void
op_finalize( model_t *       m,
             fuzz_cursor_t * cur ) {
  ushort fork_id = model_pick_fork( m, cur, 1, FORK_NEW, FORK_NEW );
  if( FD_UNLIKELY( fork_id==USHORT_MAX ) ) return;

  fd_hash_t blockhash[ 1 ];
  model_make_finalize_hash( m, cur, fork_id, blockhash );
  ulong offset = fuzz_bounded( cur, 13UL );

  fd_txncache_finalize_fork( m->tc, (fd_txncache_fork_id_t){ .val = fork_id }, offset, blockhash->uc );
  m->fork[ fork_id ].frozen         = FORK_FINAL;
  m->fork[ fork_id ].blockhash      = *blockhash;
  m->fork[ fork_id ].txnhash_offset = offset;
}

static void
op_insert( model_t *       m,
           fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( m->txn_cnt>=FUZZ_MAX_MODEL_TXNS ) ) return;

  ushort fork_id = model_pick_fork( m, cur, 1, FORK_NEW, FORK_HASHED );
  if( FD_UNLIKELY( fork_id==USHORT_MAX ) ) return;

  ushort block_fork = model_pick_strict_ancestor( m, cur, fork_id, 0 );
  if( FD_UNLIKELY( block_fork==USHORT_MAX ) ) return;

  fd_hash_t txnhash[ 1 ];
  hash_from_seed( txnhash, 0x7A58000000000000UL, ++m->hash_nonce, fuzz_u8( cur ) );

  fd_txncache_insert( m->tc,
                      (fd_txncache_fork_id_t){ .val = fork_id },
                      m->fork[ block_fork ].blockhash.uc,
                      txnhash->uc );

  model_txn_t * txn = &m->txn[ m->txn_cnt++ ];
  txn->used       = 1;
  txn->block_fork = block_fork;
  txn->txn_fork   = fork_id;
  txn->generation = m->fork[ fork_id ].generation;
  txn->txnhash    = *txnhash;
}

static void
op_query( model_t *       m,
          fuzz_cursor_t * cur ) {
  ushort fork_id = model_pick_fork( m, cur, 1, FORK_NEW, FORK_FINAL );
  if( FD_UNLIKELY( fork_id==USHORT_MAX ) ) return;

  ushort block_fork = model_pick_strict_ancestor( m, cur, fork_id, 1 );
  if( FD_UNLIKELY( block_fork==USHORT_MAX ) ) return;

  fd_hash_t txnhash[ 1 ];
  int use_existing = (m->txn_cnt && (fuzz_u8( cur ) & 1U));
  if( use_existing ) {
    *txnhash = m->txn[ fuzz_bounded( cur, m->txn_cnt ) ].txnhash;
  } else {
    hash_from_seed( txnhash, 0xAB53000000000000UL, ++m->hash_nonce, fuzz_u8( cur ) );
  }

  int actual = fd_txncache_query( m->tc,
                                  (fd_txncache_fork_id_t){ .val = fork_id },
                                  m->fork[ block_fork ].blockhash.uc,
                                  txnhash->uc );
  int expect = model_query( m, fork_id, block_fork, txnhash );
  FD_TEST( actual==expect );
}

static void
op_cancel( model_t *       m,
           fuzz_cursor_t * cur ) {
  ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
  ulong  candidate_cnt = 0UL;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !m->fork[ i ].alive ) ) continue;
    if( FD_UNLIKELY( i==m->current_root ) ) continue;
    if( FD_UNLIKELY( m->fork[ i ].parent==USHORT_MAX ) ) continue;
    if( FD_UNLIKELY( !model_descends( m, (ushort)i, m->current_root ) ) ) continue;
    candidate[ candidate_cnt++ ] = (ushort)i;
  }

  if( FD_UNLIKELY( !candidate_cnt ) ) return;

  ushort fork_id = candidate[ fuzz_bounded( cur, candidate_cnt ) ];
  fd_txncache_cancel_fork( m->tc, (fd_txncache_fork_id_t){ .val = fork_id } );
  model_remove_subtree( m, fork_id );
}

/* model_advance_to mirrors the model side of fd_txncache_advance_root:
   prune the old root's other subtrees, append the new root to the root
   history, and -- once the blockhash-distance window is full -- evict
   the oldest root and detach the new window head. */

static void
model_advance_to( model_t * m,
                  ushort    new_root ) {
  ushort old_root = m->current_root;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( m->fork[ i ].alive && m->fork[ i ].parent==old_root && i!=new_root )
      model_remove_subtree( m, (ushort)i );
  }

  m->current_root = new_root;
  FD_TEST( m->roots_tail<FUZZ_ROOT_HISTORY_MAX );
  m->roots[ m->roots_tail++ ] = new_root;
  m->root_cnt++;

  if( FD_UNLIKELY( m->root_cnt>FD_TXNCACHE_MAX_BLOCKHASH_DISTANCE ) ) {
    ushort evicted = m->roots[ m->roots_head++ ];
    FD_TEST( m->roots_head<m->roots_tail );
    ushort new_head = m->roots[ m->roots_head ];
    model_remove_only( m, evicted );
    if( m->fork[ new_head ].alive ) m->fork[ new_head ].parent = USHORT_MAX;
    m->root_cnt--;
  }
}

static void
op_advance_root( model_t *       m,
                 fuzz_cursor_t * cur ) {
  ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
  ulong  candidate_cnt = 0UL;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !m->fork[ i ].alive ) ) continue;
    if( FD_UNLIKELY( m->fork[ i ].frozen!=FORK_FINAL ) ) continue;
    if( m->fork[ i ].parent==m->current_root ) candidate[ candidate_cnt++ ] = (ushort)i;
  }

  if( FD_UNLIKELY( !candidate_cnt ) ) return;

  ushort new_root = candidate[ fuzz_bounded( cur, candidate_cnt ) ];
  fd_txncache_advance_root( m->tc, (fd_txncache_fork_id_t){ .val = new_root } );
  model_advance_to( m, new_root );
}

/* op_extend_root grows the root chain by one in a single operation
   (attach a child off the root, finalize it, advance the root onto it).
   A run of this op drives root_cnt past FD_TXNCACHE_MAX_BLOCKHASH_DISTANCE
   so the root-eviction path is reached. */

static void
op_extend_root( model_t *       m,
                fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( model_current_tree_cnt( m )>=m->max_live_slots ) ) return;
  if( FD_UNLIKELY( !blockcache_pool_free( m->tc->blockcache_shmem_pool ) ) ) return;

  ushort parent = m->current_root;
  fd_txncache_fork_id_t child = fd_txncache_attach_child( m->tc, (fd_txncache_fork_id_t){ .val = parent } );
  model_add_fork( m, child, parent, m->tc->blockcache_pool[ child.val ].shmem->generation );

  fd_hash_t blockhash[ 1 ];
  model_make_finalize_hash( m, cur, child.val, blockhash );
  ulong offset = fuzz_bounded( cur, 13UL );
  fd_txncache_finalize_fork( m->tc, child, offset, blockhash->uc );
  m->fork[ child.val ].frozen         = FORK_FINAL;
  m->fork[ child.val ].blockhash      = *blockhash;
  m->fork[ child.val ].txnhash_offset = offset;

  fd_txncache_advance_root( m->tc, child );
  model_advance_to( m, child.val );
}

static void
fuzz_cleanup( void ) {
  free( fuzz_shmem );
  free( fuzz_ljoin );
}

int
LLVMFuzzerInitialize( int *    argc,
                      char *** argv ) {
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );
  fd_boot( argc, argv );
  fd_log_level_core_set( 3 );
  fd_log_level_stderr_set( 4 );
  fd_log_level_logfile_set( 4 );
  atexit( fd_halt );

  fuzz_shmem_fp = fd_txncache_shmem_footprint( FUZZ_MAX_LIVE_SLOTS, FUZZ_MAX_TXN_PER_SLOT );
  fuzz_ljoin_fp = fd_txncache_footprint( FUZZ_MAX_LIVE_SLOTS );
  FD_TEST( fuzz_shmem_fp );
  FD_TEST( fuzz_ljoin_fp );

  ulong shmem_align = fd_txncache_shmem_align();
  ulong ljoin_align = fd_txncache_align();
  fuzz_shmem = aligned_alloc( shmem_align, FD_ULONG_ALIGN_UP( fuzz_shmem_fp, shmem_align ) );
  fuzz_ljoin = aligned_alloc( ljoin_align, FD_ULONG_ALIGN_UP( fuzz_ljoin_fp, ljoin_align ) );
  FD_TEST( fuzz_shmem );
  FD_TEST( fuzz_ljoin );
  atexit( fuzz_cleanup );

  return 0;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {
  if( FD_UNLIKELY( !size ) ) return 0;

  fuzz_cursor_t cur = { .cur = data, .rem = size };

  static ulong const txn_per_slot_choice[] = { 1UL, 2UL, 4UL, 16UL, 64UL, 256UL };
  ulong max_live_slots   = 2UL + fuzz_bounded( &cur, FUZZ_MAX_LIVE_SLOTS-1UL );
  ulong max_txn_per_slot = txn_per_slot_choice[ fuzz_bounded( &cur, sizeof(txn_per_slot_choice)/sizeof(txn_per_slot_choice[0]) ) ];

  fd_txncache_t * tc = setup( max_live_slots, max_txn_per_slot );

  model_t * model = fuzz_model;
  model_init( model, tc, max_live_slots );
  check_cache_invariants( model );

  /* One operation per step until the input is consumed (bounded by a
     safety cap).  The program length, and therefore which deep states
     are reached, is driven entirely by the input. */
  for( ulong action_idx=0UL; action_idx<FUZZ_MAX_ACTIONS && cur.rem; action_idx++ ) {
    switch( fuzz_u8( &cur ) & 15U ) {
      case  0U:
      case  1U:
      case  2U: op_attach          ( model, &cur ); break;
      case  3U: op_attach_blockhash( model, &cur ); break;
      case  4U:
      case  5U:
      case  6U: op_insert          ( model, &cur ); break;
      case  7U:
      case  8U: op_query           ( model, &cur ); break;
      case  9U:
      case 10U: op_finalize        ( model, &cur ); break;
      case 11U: op_cancel          ( model, &cur ); break;
      case 12U: op_advance_root    ( model, &cur ); break;
      default:  op_extend_root     ( model, &cur ); break;
    }

    check_cache_invariants( model );
  }

  return 0;
}
