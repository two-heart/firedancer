#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#if !FD_HAS_ATOMIC
#error "This target requires FD_HAS_ATOMIC"
#endif

#include <stdlib.h>
#include <string.h>

#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"
#include "fd_txncache.h"
#include "fd_txncache_private.h"

#define FUZZ_MAX_LIVE_SLOTS    (4UL)
#define FUZZ_MAX_TXN_PER_SLOT  (256UL)
#define FUZZ_MAX_ACTIVE_SLOTS  (FD_TXNCACHE_MAX_BLOCKHASH_DISTANCE+FUZZ_MAX_LIVE_SLOTS)
#define FUZZ_MAX_ACTIONS       (96UL)
#define FUZZ_MAX_MODEL_TXNS    (768UL)
#define FUZZ_ROOT_HISTORY_MAX  (FD_TXNCACHE_MAX_BLOCKHASH_DISTANCE+FUZZ_MAX_ACTIONS+4UL)

#define NULL_FORK ((fd_txncache_fork_id_t){ .val = USHORT_MAX })

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
  ulong         salt;
} fuzz_cursor_t;

typedef struct {
  int       alive;
  int       finalized;
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
  h->ul[ 0 ] = 0x243f6a8885a308d3UL ^ tag;
  h->ul[ 1 ] = 0x13198a2e03707344UL ^ (0x9e3779b97f4a7c15UL*a);
  h->ul[ 2 ] = 0xa4093822299f31d0UL ^ (0xbf58476d1ce4e5b9UL*b);
  h->ul[ 3 ] = 0x082efa98ec4e6c89UL ^ (tag + 0x94d049bb133111ebUL*(a+b+1UL));
}

static uchar
fuzz_u8( fuzz_cursor_t * cur ) {
  if( FD_LIKELY( cur->rem ) ) {
    uchar v = cur->cur[ 0 ];
    cur->cur++;
    cur->rem--;
    return v;
  }

  cur->salt = 6364136223846793005UL*cur->salt + 1442695040888963407UL;
  return (uchar)(cur->salt >> 56);
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
setup_cache( ulong max_live_slots,
             ulong max_txn_per_slot ) {
  FD_TEST( max_live_slots  <=FUZZ_MAX_LIVE_SLOTS   );
  FD_TEST( max_txn_per_slot<=FUZZ_MAX_TXN_PER_SLOT );

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

static ushort
model_pick_fork( model_t const * m,
                 fuzz_cursor_t * cur,
                 int             want_current_tree,
                 int             want_unfinalized,
                 int             want_finalized ) {
  ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
  ulong  candidate_cnt = 0UL;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !m->fork[ i ].alive ) ) continue;
    if( want_current_tree && !model_in_current_tree( m, (ushort)i ) ) continue;
    if( want_unfinalized &&  m->fork[ i ].finalized ) continue;
    if( want_finalized   && !m->fork[ i ].finalized ) continue;
    candidate[ candidate_cnt++ ] = (ushort)i;
  }

  if( FD_UNLIKELY( !candidate_cnt ) ) return USHORT_MAX;
  return candidate[ fuzz_bounded( cur, candidate_cnt ) ];
}

static ushort
model_pick_parent( model_t const * m,
                   fuzz_cursor_t * cur ) {
  ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
  ulong  candidate_cnt = 0UL;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !m->fork[ i ].alive     ) ) continue;
    if( FD_UNLIKELY( !m->fork[ i ].finalized ) ) continue;
    if( FD_UNLIKELY( !model_in_current_tree( m, (ushort)i ) ) ) continue;
    candidate[ candidate_cnt++ ] = (ushort)i;
  }

  if( FD_UNLIKELY( !candidate_cnt ) ) return USHORT_MAX;
  return candidate[ fuzz_bounded( cur, candidate_cnt ) ];
}

static ushort
model_pick_strict_ancestor_with_blockhash( model_t const * m,
                                           fuzz_cursor_t * cur,
                                           ushort          fork_id ) {
  ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
  ulong  candidate_cnt = 0UL;

  for( ushort cur_id=m->fork[ fork_id ].parent; cur_id!=USHORT_MAX; cur_id=m->fork[ cur_id ].parent ) {
    if( FD_UNLIKELY( !m->fork[ cur_id ].alive     ) ) break;
    if( FD_UNLIKELY( !m->fork[ cur_id ].finalized ) ) continue;
    candidate[ candidate_cnt++ ] = cur_id;
  }

  if( FD_UNLIKELY( !candidate_cnt ) ) return USHORT_MAX;
  return candidate[ fuzz_bounded( cur, candidate_cnt ) ];
}

static int
model_hash_on_strict_ancestry( model_t const * m,
                               ushort          fork_id,
                               fd_hash_t const * blockhash ) {
  for( ushort cur_id=m->fork[ fork_id ].parent; cur_id!=USHORT_MAX; cur_id=m->fork[ cur_id ].parent ) {
    if( FD_UNLIKELY( !m->fork[ cur_id ].alive ) ) break;
    if( m->fork[ cur_id ].finalized && fd_hash_eq( &m->fork[ cur_id ].blockhash, blockhash ) ) return 1;
  }
  return 0;
}

static void
model_make_finalize_hash( model_t *      m,
                          fuzz_cursor_t * cur,
                          ushort         fork_id,
                          fd_hash_t *    blockhash ) {
  int duplicate = !(fuzz_u8( cur ) & 3U);
  if( duplicate ) {
    ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
    ulong  candidate_cnt = 0UL;
    for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
      if( FD_UNLIKELY( !m->fork[ i ].alive     ) ) continue;
      if( FD_UNLIKELY( !m->fork[ i ].finalized ) ) continue;
      if( FD_UNLIKELY( i==fork_id || model_descends( m, fork_id, (ushort)i ) ) ) continue;
      candidate[ candidate_cnt++ ] = (ushort)i;
    }
    if( candidate_cnt ) {
      ushort src = candidate[ fuzz_bounded( cur, candidate_cnt ) ];
      *blockhash = m->fork[ src ].blockhash;
      FD_FUZZ_MUST_BE_COVERED;
      return;
    }
  }

  do {
    hash_from_seed( blockhash, 0xB10C000000000000UL, ++m->hash_nonce, fork_id );
  } while( model_hash_on_strict_ancestry( m, fork_id, blockhash ) );
}

static void
model_add_fork( model_t *            m,
                fd_txncache_fork_id_t fork_id,
                ushort                parent,
                uint                  generation ) {
  FD_TEST( fork_id.val<FUZZ_MAX_ACTIVE_SLOTS );
  model_fork_t * fork = &m->fork[ fork_id.val ];
  memset( fork, 0, sizeof(*fork) );
  fork->alive      = 1;
  fork->finalized  = 0;
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
model_init( model_t *      m,
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

  m->fork[ root.val ].finalized       = 1;
  m->fork[ root.val ].blockhash       = *blockhash;
  m->fork[ root.val ].txnhash_offset  = 0UL;
  m->current_root                     = root.val;
  m->roots[ m->roots_tail++ ]         = root.val;
}

static int
model_query( model_t const * m,
             ushort          fork_id,
             ushort          block_fork,
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

static void
check_cache_invariants( model_t const * m ) {
  fd_txncache_t * tc = m->tc;
  FD_TEST( tc->shmem->txnpages_free_cnt<=tc->shmem->max_txnpages );
  FD_TEST( tc->shmem->max_txnpages<=512U );

  ulong pool_free = blockcache_pool_free( tc->blockcache_shmem_pool );
  FD_TEST( pool_free + m->live_cnt == blockcache_pool_max( tc->blockcache_shmem_pool ) );

  uchar page_seen[ 512 ];
  memset( page_seen, 0, sizeof(page_seen) );
  ulong used_pages = 0UL;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !m->fork[ i ].alive ) ) continue;

    fuzz_blockcache_private_t const * bc = &tc->blockcache_pool[ i ];
    FD_TEST( bc->shmem->frozen>=0 );
    FD_TEST( bc->shmem->generation==m->fork[ i ].generation );
    FD_TEST( bc->shmem->pages_cnt<=tc->shmem->txnpages_per_blockhash_max );

    if( m->fork[ i ].finalized ) FD_TEST( bc->shmem->frozen==2 );
    else                         FD_TEST( bc->shmem->frozen<=1 );

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

  for( ulong parent_id=0UL; parent_id<FUZZ_MAX_ACTIVE_SLOTS; parent_id++ ) {
    if( FD_UNLIKELY( !m->fork[ parent_id ].alive ) ) continue;

    uchar reached[ FUZZ_MAX_ACTIVE_SLOTS ];
    memset( reached, 0, sizeof(reached) );

    int parent_is_current_tree = model_in_current_tree( m, (ushort)parent_id );
    ushort child_id = tc->blockcache_pool[ parent_id ].shmem->child_id.val;
    for( ulong depth=0UL; child_id!=USHORT_MAX && depth<FUZZ_MAX_ACTIVE_SLOTS; depth++ ) {
      if( FD_UNLIKELY( child_id>=FUZZ_MAX_ACTIVE_SLOTS ) ) FD_TEST( 0 );
      fuzz_blockcache_private_t const * child = &tc->blockcache_pool[ child_id ];
      if( FD_UNLIKELY( !m->fork[ child_id ].alive ||
                       child->shmem->frozen<0     ||
                       m->fork[ child_id ].parent!=(ushort)parent_id ) ) {
        FD_FUZZ_MUST_BE_COVERED;
        if( parent_is_current_tree ) FD_TEST( 0 );
        child_id = USHORT_MAX;
        break;
      }
      FD_TEST( !reached[ child_id ] );
      reached[ child_id ] = 1U;
      child_id = child->shmem->sibling_id.val;
    }
    if( FD_UNLIKELY( child_id!=USHORT_MAX ) ) FD_TEST( 0 );

    if( parent_is_current_tree ) {
      for( ulong child_id2=0UL; child_id2<FUZZ_MAX_ACTIVE_SLOTS; child_id2++ ) {
        if( m->fork[ child_id2 ].alive && m->fork[ child_id2 ].parent==(ushort)parent_id )
          FD_TEST( reached[ child_id2 ] );
      }
    }
  }
}

static void
op_attach( model_t *      m,
           fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( model_current_tree_cnt( m )>=m->max_live_slots ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  ushort parent = model_pick_parent( m, cur );
  if( FD_UNLIKELY( parent==USHORT_MAX ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  fd_txncache_fork_id_t child = fd_txncache_attach_child( m->tc, (fd_txncache_fork_id_t){ .val = parent } );
  model_add_fork( m, child, parent, m->tc->blockcache_pool[ child.val ].shmem->generation );
  FD_FUZZ_MUST_BE_COVERED;
}

static void
op_finalize( model_t *      m,
             fuzz_cursor_t * cur ) {
  ushort fork_id = model_pick_fork( m, cur, 1, 1, 0 );
  if( FD_UNLIKELY( fork_id==USHORT_MAX ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  fd_hash_t blockhash[ 1 ];
  model_make_finalize_hash( m, cur, fork_id, blockhash );
  ulong offset = fuzz_bounded( cur, 13UL );

  fd_txncache_finalize_fork( m->tc, (fd_txncache_fork_id_t){ .val = fork_id }, offset, blockhash->uc );
  m->fork[ fork_id ].finalized      = 1;
  m->fork[ fork_id ].blockhash      = *blockhash;
  m->fork[ fork_id ].txnhash_offset = offset;
  FD_FUZZ_MUST_BE_COVERED;
}

static void
op_insert( model_t *      m,
           fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( m->txn_cnt>=FUZZ_MAX_MODEL_TXNS ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  ushort fork_id = model_pick_fork( m, cur, 1, 1, 0 );
  if( FD_UNLIKELY( fork_id==USHORT_MAX ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  ushort block_fork = model_pick_strict_ancestor_with_blockhash( m, cur, fork_id );
  if( FD_UNLIKELY( block_fork==USHORT_MAX ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

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
  FD_FUZZ_MUST_BE_COVERED;
}

static void
op_query( model_t *      m,
          fuzz_cursor_t * cur ) {
  ushort fork_id = model_pick_fork( m, cur, 1, 0, 0 );
  if( FD_UNLIKELY( fork_id==USHORT_MAX ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  ushort block_fork = model_pick_strict_ancestor_with_blockhash( m, cur, fork_id );
  if( FD_UNLIKELY( block_fork==USHORT_MAX ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

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

  FD_FUZZ_MUST_BE_COVERED;
  if( actual ) FD_FUZZ_MUST_BE_COVERED;
  else         FD_FUZZ_MUST_BE_COVERED;
}

static void
op_cancel( model_t *      m,
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

  if( FD_UNLIKELY( !candidate_cnt ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  ushort fork_id = candidate[ fuzz_bounded( cur, candidate_cnt ) ];
  fd_txncache_cancel_fork( m->tc, (fd_txncache_fork_id_t){ .val = fork_id } );
  model_remove_subtree( m, fork_id );
  FD_FUZZ_MUST_BE_COVERED;
}

static void
op_advance_root( model_t *      m,
                 fuzz_cursor_t * cur ) {
  ushort candidate[ FUZZ_MAX_ACTIVE_SLOTS ];
  ulong  candidate_cnt = 0UL;

  for( ulong i=0UL; i<FUZZ_MAX_ACTIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !m->fork[ i ].alive ) ) continue;
    if( FD_UNLIKELY( !m->fork[ i ].finalized ) ) continue;
    if( m->fork[ i ].parent==m->current_root ) candidate[ candidate_cnt++ ] = (ushort)i;
  }

  if( FD_UNLIKELY( !candidate_cnt ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  ushort new_root = candidate[ fuzz_bounded( cur, candidate_cnt ) ];
  ushort old_root = m->current_root;

  fd_txncache_advance_root( m->tc, (fd_txncache_fork_id_t){ .val = new_root } );

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
    FD_FUZZ_MUST_BE_COVERED;
  }

  FD_FUZZ_MUST_BE_COVERED;
}

static void
run_actor_program( uchar const * data,
                   ulong         size ) {
  fuzz_cursor_t cur = { .cur = data, .rem = size, .salt = size ^ 0x123456789abcdef0UL };

  static ulong const txn_per_slot_choice[] = { 1UL, 2UL, 4UL, 16UL, 64UL, 256UL };
  ulong max_live_slots   = 2UL + fuzz_bounded( &cur, FUZZ_MAX_LIVE_SLOTS-1UL );
  ulong max_txn_per_slot = txn_per_slot_choice[ fuzz_bounded( &cur, sizeof(txn_per_slot_choice)/sizeof(txn_per_slot_choice[0]) ) ];

  fd_txncache_t * tc = setup_cache( max_live_slots, max_txn_per_slot );

  model_t * model = fuzz_model;
  model_init( model, tc, max_live_slots );

  ulong action_cnt = 1UL + fuzz_bounded( &cur, FUZZ_MAX_ACTIONS );
  for( ulong action_idx=0UL; action_idx<action_cnt; action_idx++ ) {
    uchar action = (uchar)(fuzz_u8( &cur ) % 12U);
    switch( action ) {
      case 0U:
      case 1U:
      case 2U: op_attach( model, &cur );       break;
      case 3U:
      case 4U:
      case 5U: op_insert( model, &cur );       break;
      case 6U:
      case 7U: op_query( model, &cur );        break;
      case 8U: op_finalize( model, &cur );     break;
      case 9U: op_cancel( model, &cur );       break;
      default: op_advance_root( model, &cur ); break;
    }

    check_cache_invariants( model );
  }
}

static void
run_stale_child_link_seed( void ) {
  fd_txncache_t * tc = setup_cache( 4UL, 4UL );

  model_t * model = fuzz_model;
  model_init( model, tc, 4UL );

  fd_txncache_fork_id_t winner = fd_txncache_attach_child( tc, (fd_txncache_fork_id_t){ .val = model->current_root } );
  model_add_fork( model, winner, model->current_root, tc->blockcache_pool[ winner.val ].shmem->generation );

  fd_txncache_fork_id_t loser = fd_txncache_attach_child( tc, (fd_txncache_fork_id_t){ .val = model->current_root } );
  model_add_fork( model, loser, model->current_root, tc->blockcache_pool[ loser.val ].shmem->generation );

  fd_hash_t txn[ 1 ];
  hash_from_seed( txn, 0x57A1E00000000000UL, 0UL, 0UL );
  fd_txncache_insert( tc, winner, model->fork[ model->current_root ].blockhash.uc, txn->uc );

  fd_hash_t blockhash[ 1 ];
  hash_from_seed( blockhash, 0xB10C000000000000UL, 1UL, 0UL );
  fd_txncache_finalize_fork( tc, winner, 0UL, blockhash->uc );
  model->fork[ winner.val ].finalized = 1;
  model->fork[ winner.val ].blockhash = *blockhash;

  hash_from_seed( blockhash, 0xB10C000000000000UL, 2UL, 0UL );
  fd_txncache_finalize_fork( tc, loser, 0UL, blockhash->uc );
  model->fork[ loser.val ].finalized = 1;
  model->fork[ loser.val ].blockhash = *blockhash;

  fd_txncache_advance_root( tc, winner );
  model_remove_subtree( model, loser.val );
  model->current_root = winner.val;
  model->roots[ model->roots_tail++ ] = winner.val;
  model->root_cnt++;

  FD_TEST( fd_txncache_query( tc, winner, model->fork[ model->roots[ model->roots_head ] ].blockhash.uc, txn->uc ) );
  check_cache_invariants( model );
  FD_FUZZ_MUST_BE_COVERED;
}

static void
run_page_exhaustion_seed( void ) {
  fd_txncache_t * tc = setup_cache( 4UL, 4UL );

  fd_hash_t root_hash[ 1 ];
  hash_from_seed( root_hash, 0xB10C000000000000UL, 0UL, 0UL );

  fd_txncache_fork_id_t root = fd_txncache_attach_child( tc, NULL_FORK );
  fd_txncache_finalize_fork( tc, root, 0UL, root_hash->uc );

  fd_txncache_fork_id_t prev = root;

  ulong const stale_rounds         = 130UL;
  ulong const stale_txns_per_round = 126UL;
  ulong const total_stale          = stale_rounds*stale_txns_per_round;
  ulong const valid_pre_purge      = FD_TXNCACHE_TXNS_PER_PAGE-total_stale;
  ulong const stale_id_base        = 1000000UL;

  for( ulong i=0UL; i<stale_rounds; i++ ) {
    fd_txncache_fork_id_t loser  = fd_txncache_attach_child( tc, prev );
    fd_txncache_fork_id_t winner = fd_txncache_attach_child( tc, prev );

    for( ulong j=0UL; j<stale_txns_per_round; j++ ) {
      fd_hash_t txnhash[ 1 ];
      hash_from_seed( txnhash, 0x57A1E00000000000UL, stale_id_base+i*stale_txns_per_round+j, 0UL );
      fd_txncache_insert( tc, loser, root_hash->uc, txnhash->uc );
    }

    fd_hash_t blockhash[ 1 ];
    hash_from_seed( blockhash, 0xB10C000000000000UL, 10000UL+i, 0UL );
    fd_txncache_finalize_fork( tc, loser, 0UL, blockhash->uc );

    hash_from_seed( blockhash, 0xB10C000000000000UL, i+1UL, 0UL );
    fd_txncache_finalize_fork( tc, winner, 0UL, blockhash->uc );
    fd_txncache_advance_root( tc, winner );

    prev = winner;
  }

  FD_TEST( valid_pre_purge==4UL );
  fd_txncache_fork_id_t query_fork = fd_txncache_attach_child( tc, prev );

  for( ulong i=0UL; i<valid_pre_purge; i++ ) {
    fd_hash_t txnhash[ 1 ];
    hash_from_seed( txnhash, 0x600D000000000000UL, i, 0UL );
    fd_txncache_insert( tc, query_fork, root_hash->uc, txnhash->uc );
  }

  fd_hash_t trigger[ 1 ];
  hash_from_seed( trigger, 0x600D000000000000UL, valid_pre_purge, 0UL );
  fd_txncache_insert( tc, query_fork, root_hash->uc, trigger->uc );
  FD_FUZZ_MUST_BE_COVERED;

  for( ulong i=0UL; i<=valid_pre_purge; i++ ) {
    fd_hash_t txnhash[ 1 ];
    hash_from_seed( txnhash, 0x600D000000000000UL, i, 0UL );
    FD_TEST( fd_txncache_query( tc, query_fork, root_hash->uc, txnhash->uc ) );
  }

  for( ulong i=0UL; i<8UL; i++ ) {
    fd_hash_t txnhash[ 1 ];
    hash_from_seed( txnhash, 0x57A1E00000000000UL, stale_id_base+i, 0UL );
    FD_TEST( !fd_txncache_query( tc, query_fork, root_hash->uc, txnhash->uc ) );
  }

  FD_TEST( tc->shmem->txnpages_free_cnt<=tc->shmem->max_txnpages );
  FD_FUZZ_MUST_BE_COVERED;
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

  if( data[ 0 ]==0xF0U ) {
    run_stale_child_link_seed();
    return 0;
  }

  if( data[ 0 ]==0xF1U ) {
    run_page_exhaustion_seed();
    return 0;
  }

  run_actor_program( data, size );
  return 0;
}
