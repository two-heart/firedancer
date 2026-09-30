// TODO I care more about what the test can catch and what it can't. 
  // 
/* test_ag_votor_scenarios drives a votor wired to a pool, as the votor
   tile does, through scenarios and checks its invariants.

     test_ag_votor_scenarios [--jobs N] [<file|dir|pattern>...]

   With no inputs, runs the JSON files in src/choreo/votor/scenarios
   from the repository root.  Quoted patterns are expanded with glob, avoiding
   the OS argument-size limit when launching with large corpora.

   A scenario is a JSON list of actions on a block tree:

     [ { "node": "1a", "parent": "0",  "action": "NOTARIZE_CERT"  },
       { "action": "CLOCK", "ms": 100 },
       { "node": "2b", "parent": "1a", "action": "REPLAY_COMPLETE" } ]

   Labels are a slot, then the block's index in letters (a, ..., z, aa).
   The canonical chain runs from the root to the leftmost deepest block
   that is not skipped.

   Scenarios run in N forked workers.  The first failure stops the
   suite: its worker logs the backtrace, then the suite prints the
   failing input and exits nonzero.

   Inputs are scanned once before fork to size reusable storage for
   every worker.  Keep the corpus unchanged during a run; workers
   read each input again and reuse their preallocated buffers.

   Slot storage is fully initialized on first use, then sparsely reset for
   this test's single voting validator.

   Every validator signs with one fake signature.  This test's pool
   checks certificate stake thresholds but skips signature verification. */

#include <execinfo.h>
#include <fcntl.h>
#include <glob.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include "ag_cert.c" /* reuses the production stake threshold check */

static int
test_cert_verify( ag_cert_t const *       cert,
                  ag_epoch_info_t const * epoch_info ) {
  return check_threshold( cert, epoch_info );
}

#include "ag_slot_state.c" /* reuses the production vote-map queries and full reset */

static void test_slot_state_null( ag_slot_state_t * self );

/* Override verification and slot reset only in this test's pool. */
#define ag_cert_verify     test_cert_verify
#define ag_slot_state_null test_slot_state_null
#include "ag_pool.c" /* reads the pool's finality tracker */
#undef ag_cert_verify
#undef ag_slot_state_null
#include "ag_votor.h"
#include "test_ag_cert_builder.h"
#include "../../ballet/json/fd_jtok.h"
#include "../../util/io/fd_io.h"
#include "../../util/log/fd_backtrace.h"

#define VALIDATOR_CNT          (20UL)
#define QUORUM_SIGNERS         (11UL) /* validators 1 to 11, 63.4% of stake */
#define STRONG_QUORUM_SIGNERS  (16UL) /* validators 1 to 16, 82.4% of stake */
#define FALLBACK_NOTAR_SIGNERS (5UL)  /* of a notar fallback cert's signers, how many vote notar */
#define SHRED_VERSION          ((ushort)0x5a5a)
#define NS_PER_SLOT            (400000000L)
#define NS_EVERY_TIMEOUT       (1000000000000L)

enum { NOTARIZE_CERT, FINALIZE_CERT, NOTAR_FALLBACK_CERT, FAST_FINALIZE_CERT, SKIP_CERT,
       REPLAY_ARRIVES, REPLAY_COMPLETE, REPLAY_DEAD, CLOCK, ACTION_KIND_CNT };

#define CERT_CNT (REPLAY_ARRIVES)

static char const * const action_kind_name[ ACTION_KIND_CNT ] = {
  "NOTARIZE_CERT", "FINALIZE_CERT", "NOTAR_FALLBACK_CERT", "FAST_FINALIZE_CERT", "SKIP_CERT",
  "REPLAY_ARRIVES", "REPLAY_COMPLETE", "REPLAY_DEAD", "CLOCK"
};

enum { CANONICAL_NONE, CANONICAL_BLOCK, CANONICAL_SKIP };

typedef struct {
  ulong slot;
  ulong index;
} label_t;

typedef struct {
  uint    kind;
  label_t label;
  label_t parent;
  ulong   ms;
} action_t;

typedef struct {
  label_t       label;
  label_t       parent;
  uint          kinds;           /* bit per action kind, 0 if no action names the node */
  int           replayed;
  int           dead;
  ag_block_id_t replayed_parent;
} node_t;

typedef struct {
  int             canonical; /* CANONICAL_* */
  ag_block_id_t   canonical_block;
  int             voted_notar;
  int             voted_skip;
  int             voted_final;
  ag_block_hash_t voted_notar_hash;
} slot_t;

typedef struct {
  action_t * actions;
  ulong      action_cnt;
  node_t *   nodes;           /* by slot, then index */
  ulong      node_cnt;
  ulong      width;           /* highest index+1 */
  ulong      slot_cnt;        /* the root's slot to the deepest */
  ulong      vote_slot_cnt;
  slot_t *   slots;           /* vote_slot_cnt of them */
  ulong      canonical_final; /* deepest directly finalized canonical slot */
} scenario_t;

/* Sized once from the corpus before fork.  Each worker inherits private
   storage and reuses it for every scenario. */

static struct {
  uchar *    data;
  ulong      data_max;
  action_t * actions;
  ulong      action_max;
  node_t *   nodes;
  ulong      node_max;
  slot_t *   slots;
  ulong      vote_slot_max;
  void *     pool;
  ulong      pool_sz;
  void *     votor;
  ulong      votor_sz;
  ulong      pool_slot_max;
  slot_state_ele_t * slot_pool;
  uchar *           slot_initialized;
} memory;

static ag_epoch_info_t epoch_info;
static fd_bls_sig_t    fake_sig;
static ag_cert_t       templates[ CERT_CNT ];
static fd_bls_set_t    bad[ fd_bls_set_word_cnt ];

/* Only rank zero contributes individual votes; certificates do not populate
   the vote maps.  Its own notar hash and fallback hashes therefore name every
   live map entry.  Clear those keys and rank zero's sentinels on reuse, keeping
   the same counters, aggregates and certificate sentinels as the full reset.

   Slots that have never been initialized, or whose storage was overwritten
   by a smaller pool's bookkeeping, take the production reset first. */

static void
test_slot_state_null( ag_slot_state_t * self ) {
  ulong offset = (ulong)self-(ulong)&memory.slot_pool[0].slot_state;
  FD_TEST( !(offset%sizeof(slot_state_ele_t)) );
  ulong idx = offset/sizeof(slot_state_ele_t);
  FD_TEST( idx<memory.pool_slot_max );
  if( FD_UNLIKELY( !memory.slot_initialized[idx] ) ) {
    ag_slot_state_null( self );
    memory.slot_initialized[idx] = 1;
    return;
  }

  FD_TEST( self->own_rank==0UL );

  ag_slot_votes_t * votes = &self->votes;
  ag_block_hash_key_t key = FD_LOAD( ag_block_hash_key_t, votes->own_notar_hash );
  if( FD_LIKELY( !notar_map_key_inval( key ) ) ) {
    ag_slot_voted_stake_hash_t * entry = notar_map_query( votes->notar_stake_map, key, NULL );
    FD_TEST( entry );
    entry->hash = ag_block_hash_key_null;
  }

  /* Find every fallback entry before clearing any keys: clearing the first
     key in a probe chain would hide later entries that collided with it. */
  ulong cnt = votes->notar_fallback_sig_cnt[0];
  FD_TEST( cnt<=AG_NOTAR_FALLBACK_VOTE_MAX );
  ag_slot_voted_stake_hash_t * entries[ AG_NOTAR_FALLBACK_VOTE_MAX ];
  for( ulong i=0UL; i<cnt; i++ ) {
    key = FD_LOAD( ag_block_hash_key_t, votes->notar_fallback_sig_hash[0][i] );
    entries[i] = notar_fallback_map_query( votes->notar_fallback_stake_map, key, NULL );
    FD_TEST( entries[i] );
  }
  for( ulong i=0UL; i<cnt; i++ ) entries[i]->hash = ag_block_hash_key_null;

  fd_memset( &votes->notar_sig[0], 0, sizeof(fd_bls_sig_t) );
  votes->notar_fallback_sig_cnt[0] = 0;
  votes->skip_stake = 0UL;
  fd_memset( &votes->skip_sig[0], 0, sizeof(fd_bls_sig_t) );
  fd_bls_agg_null( &votes->skip_agg );
  votes->skip_fallback_stake = 0UL;
  fd_bls_agg_null( &votes->skip_fallback_agg );
  votes->finalize_stake = 0UL;
  fd_bls_agg_null( &votes->finalize_agg );
  votes->notar_or_skip_stake = 0UL;
  votes->top_notar_stake     = 0UL;
  fd_memset( votes->top_notar_hash, 0, sizeof(ag_block_hash_t) );
  fd_memset( votes->own_notar_hash, 0, sizeof(ag_block_hash_t) );

  self->certs.notar.slot         = ULONG_MAX;
  self->certs.notar_fallback_cnt = 0UL;
  self->certs.skip.slot          = ULONG_MAX;
  self->certs.fast_finalize.slot = ULONG_MAX;
  self->certs.finalize.slot      = ULONG_MAX;
  self->parents_cnt               = 0UL;
  self->pending_safe_to_notar.cnt = 0UL;
  self->sent_safe_to_notar.cnt    = 0UL;
  self->sent_safe_to_skip         = 0;
}

static void
fake_sign_fn( void *         ctx,
              fd_bls_sig_t * sig,
              uchar const *  msg,
              ulong          msg_sz ) {
  (void)ctx; (void)msg; (void)msg_sz;
  *sig = fake_sig;
}

static ag_block_id_t
block_id( label_t label ) {
  ag_block_id_t id = { .slot = label.slot };
  FD_STORE( ulong, id.hash,     label.slot  );
  FD_STORE( ulong, id.hash+8UL, label.index );
  return id;
}

/* Signatures are all fake_sig, so a cert's aggregates depend only on
   its signers: every cert is its kind's template, renamed. */

static ag_cert_t
cert( uint    kind,
      label_t label ) {
  ag_cert_t     c  = templates[ kind ];
  ag_block_id_t id = block_id( label );
  switch( c.kind ) {
  case AG_CERT_KIND_FINAL:          c.final.slot          = label.slot; break;
  case AG_CERT_KIND_SKIP:           c.skip.slot           = label.slot; break;
  case AG_CERT_KIND_NOTAR:          c.notar.slot          = label.slot; memcpy( c.notar.block_hash,          id.hash, sizeof(ag_block_hash_t) ); break;
  case AG_CERT_KIND_NOTAR_FALLBACK: c.notar_fallback.slot = label.slot; memcpy( c.notar_fallback.block_hash, id.hash, sizeof(ag_block_hash_t) ); break;
  case AG_CERT_KIND_FAST_FINAL:     c.fast_final.slot     = label.slot; memcpy( c.fast_final.block_hash,     id.hash, sizeof(ag_block_hash_t) ); break;
  default:                          FD_LOG_CRIT(( "unreachable" ));
  }
  return c;
}

/* Initializes the global fixtures shared by all scenarios, before workers fork:

   epoch_info: deterministic public keys, validator IDs and fixed stakes for
   the test cluster, including its total stake.

   fake_sig: validator 0's signature over "votor", reused for every vote
   regardless of signer or message.  The test skips signature verification
   while retaining certificate stake threshold checks.

   templates: one certificate per kind, with fixed signer sets, stakes,
   shred version and aggregate signatures.  Template signers exclude
   validator 0, the votor under test.  Since every vote uses fake_sig,
   aggregates depend only on the signer sets and can be built once.
   cert() copies these templates and changes the slot and block hash
   for each scenario action. */
static void
cluster_init( void ) {
  ag_validator_info_t info[ VALIDATOR_CNT ];
  for( ulong i=0UL; i<VALIDATOR_CNT; i++ ) {
    uchar ikm[ 32 ] = {0};
    FD_STORE( ulong, ikm, i );
    fd_bls_sec_t sk;
    fd_bls_sec_derive( &sk, ikm, sizeof(ikm) );
    info[i].id    = i;
    info[i].stake = i<10UL ? 620000UL : 380000UL; // TODO why these stakes should have a comment
    fd_bls_sec_to_pub( &sk, &info[i].bls_key );
    if( !i ) sec_sign_fn( &sk, &fake_sig, (uchar const *)"votor", 5UL );
  }
  epoch_info_build( &epoch_info, info, VALIDATOR_CNT );

  /* Template certificates exclude validator 0, the votor under test. */
  ulong                    slot = 1UL;
  ag_block_id_t            id   = block_id( (label_t){ .slot = slot } );
  ag_vote_final_t          final   [ QUORUM_SIGNERS ];
  ag_vote_skip_t           skip    [ QUORUM_SIGNERS ];
  ag_vote_notar_t          notar   [ STRONG_QUORUM_SIGNERS ];
  ag_vote_notar_fallback_t fallback[ QUORUM_SIGNERS-FALLBACK_NOTAR_SIGNERS ];
  for( ushort rank=1; rank<=STRONG_QUORUM_SIGNERS; rank++ ) {
    notar[ rank-1 ] = ag_vote_construct_notar( fake_sign_fn, NULL, slot, id.hash, rank, SHRED_VERSION ).notar;
    if( rank>QUORUM_SIGNERS ) continue;
    final[ rank-1 ] = ag_vote_construct_final( fake_sign_fn, NULL, slot, rank, SHRED_VERSION ).final;
    skip [ rank-1 ] = ag_vote_construct_skip ( fake_sign_fn, NULL, slot, rank, SHRED_VERSION ).skip;
    if( rank>FALLBACK_NOTAR_SIGNERS ) fallback[ rank-1-FALLBACK_NOTAR_SIGNERS ] = ag_vote_construct_notar_fallback( fake_sign_fn, NULL, slot, id.hash, rank, SHRED_VERSION ).notar_fallback;
  }
  templates[ NOTARIZE_CERT       ] = cert_build_notar         ( notar, QUORUM_SIGNERS, &epoch_info );
  templates[ FINALIZE_CERT       ] = cert_build_final         ( final, QUORUM_SIGNERS, &epoch_info );
  templates[ NOTAR_FALLBACK_CERT ] = cert_build_notar_fallback( notar, FALLBACK_NOTAR_SIGNERS, fallback, QUORUM_SIGNERS-FALLBACK_NOTAR_SIGNERS, &epoch_info );
  templates[ FAST_FINALIZE_CERT  ] = cert_build_fast_final    ( notar, STRONG_QUORUM_SIGNERS, &epoch_info );
  templates[ SKIP_CERT           ] = cert_build_skip          ( skip,  QUORUM_SIGNERS, NULL, 0UL, &epoch_info );
}

/* Parsing.  A malformed scenario is a failure. */

/* Parses "0", or a slot then letters: a is index 0, z 25, aa 26. */

static label_t
label_parse( fd_jtok_t * j ) {
  char s[ 32 ];
  fd_jtok_cstr( j, s, sizeof(s) );
  if( !strcmp( s, "0" ) ) return (label_t){ 0 };
  label_t      label = { 0 };
  char const * c     = s;
  if( FD_UNLIKELY( (*c<'1') | (*c>'9') ) ) FD_LOG_ERR(( "bad label \"%s\"", s ));
  for( ; (*c>='0') & (*c<='9'); c++ ) label.slot = label.slot*10UL + (ulong)( *c-'0' );
  if( FD_UNLIKELY( (*c<'a') | (*c>'z') ) ) FD_LOG_ERR(( "bad label \"%s\"", s ));
  for( ; (*c>='a') & (*c<='z'); c++ ) label.index = label.index*26UL + (ulong)( *c-'a' ) + 1UL;
  if( FD_UNLIKELY( *c ) ) FD_LOG_ERR(( "bad label \"%s\"", s ));
  label.index--;
  return label;
}

static uint
action_kind_parse( fd_jtok_str_t const * s ) {
  for( uint kind=0U; kind<ACTION_KIND_CNT; kind++ ) {
    if( fd_jtok_str_eq( s, action_kind_name[ kind ] ) ) return kind;
  }
  FD_LOG_ERR(( "unknown action" ));
}

static node_t *
node_find( scenario_t const * s,
           label_t            label ) {
  if( (label.slot>=s->slot_cnt) | (label.index>=s->width) ) return NULL;
  node_t * n = &s->nodes[ label.slot*s->width+label.index ];
  return n->kinds ? n : NULL;
}

/* The node a block hash names, as block_id encodes it, or NULL. */

static node_t *
node_of_block( scenario_t const * s,
               ulong              slot,
               uchar const *      hash ) {
  if( FD_LOAD( ulong, hash )!=slot ) return NULL;
  return node_find( s, (label_t){ .slot = slot, .index = FD_LOAD( ulong, hash+8UL ) } );
}

/* Parses the JSON action list, failing on any malformed action.  With
   s->actions==NULL, only measures the storage needed for the scenario. */

static void
actions_parse( scenario_t * s,
               uchar const * data,
               ulong         size ) {
  fd_jtok_t     j[1];
  fd_jtok_str_t key;
  fd_jtok_init( j, data, size );
  fd_jtok_arr_enter( j );
  while( fd_jtok_arr_next( j ) ) {
    action_t   measured;
    action_t * a = &measured;
    if( s->actions ) {
      if( FD_UNLIKELY( s->action_cnt>=memory.action_max ) ) FD_LOG_ERR(( "scenario exceeds preallocated action capacity" ));
      a = &s->actions[ s->action_cnt ];
    }
    s->action_cnt++;
    int        has_node   = 0;
    int        has_parent = 0;
    *a = (action_t){ .kind = UINT_MAX, .ms = ULONG_MAX };
    fd_jtok_obj_enter( j );
    while( fd_jtok_obj_next( j, &key ) ) {
      if(      fd_jtok_str_eq( &key, "node"   ) ) { a->label  = label_parse( j ); has_node   = 1; }
      else if( fd_jtok_str_eq( &key, "parent" ) ) { a->parent = label_parse( j ); has_parent = 1; }
      else if( fd_jtok_str_eq( &key, "ms"     ) ) fd_jtok_ulong( j, &a->ms );
      else if( fd_jtok_str_eq( &key, "action" ) ) {
        fd_jtok_str_t kind;
        fd_jtok_str( j, &kind );
        a->kind = action_kind_parse( &kind );
      }
    }
    if( FD_UNLIKELY( fd_jtok_err( j ) ) ) FD_LOG_ERR(( "malformed action %lu", s->action_cnt-1UL ));
    int ok = a->kind==CLOCK ? (!has_node) & (a->ms!=ULONG_MAX)
                            : (a->kind!=UINT_MAX) & has_node & has_parent & (!!a->label.slot) & (a->parent.slot<a->label.slot);
    if( FD_UNLIKELY( !ok ) ) FD_LOG_ERR(( "bad action %lu", s->action_cnt-1UL ));
    if( a->kind!=CLOCK ) {
      FD_TEST( (a->label.slot<ULONG_MAX) & (a->label.index<ULONG_MAX) );
      s->slot_cnt = fd_ulong_max( s->slot_cnt, a->label.slot +1UL );
      s->width    = fd_ulong_max( s->width,    a->label.index+1UL );
    }
  }
  if( FD_UNLIKELY( fd_jtok_fini( j ) ) ) FD_LOG_ERR(( "malformed JSON" ));

  /* A cert at a window's end readies the next window, so votes can reach
     the end of that window. */
  FD_TEST( s->slot_cnt<=ULONG_MAX-2UL*AG_SLOTS_PER_WINDOW );
  s->vote_slot_cnt = ( (s->slot_cnt-1UL)/AG_SLOTS_PER_WINDOW+2UL )*AG_SLOTS_PER_WINDOW;
}

/* Lays nodes out by slot then index, merging what each node's actions say. */

static void
nodes_build( scenario_t * s ) {
  if( FD_UNLIKELY( s->slot_cnt>memory.node_max/s->width ) ) FD_LOG_ERR(( "scenario exceeds preallocated node capacity" ));
  memset( s->nodes, 0, s->slot_cnt*s->width*sizeof(node_t) );
  for( ulong i=0UL; i<s->action_cnt; i++ ) {
    action_t const * a = &s->actions[i];
    if( a->kind==CLOCK ) continue;
    node_t * n   = &s->nodes[ a->label.slot*s->width+a->label.index ];
    s->node_cnt += !n->kinds;
    n->label     = a->label;
    n->parent    = a->parent;
    n->kinds    |= 1U<<a->kind;
  }
}

/* A canonical block is directly finalized by a notar and final cert, or
   a fast final cert.  Slots the chain jumps over are skipped. */

static void
canonical_build( scenario_t * s ) {
  node_t const * n = NULL;
  for( ulong slot=s->slot_cnt-1UL; (!!slot) & (!n); slot-- ) {
    for( ulong index=0UL; (index<s->width) & (!n); index++ ) {
      node_t const * c = node_find( s, (label_t){ .slot = slot, .index = index } );
      if( c && !( c->kinds & (1U<<SKIP_CERT) ) ) n = c;
    }
  }

  for( ; n; n = n->parent.slot ? node_find( s, n->parent ) : NULL ) {
    uint k      = n->kinds;
    int  direct = ( (!!( k & (1U<<NOTARIZE_CERT) )) & (!!( k & (1U<<FINALIZE_CERT) )) ) | (!!( k & (1U<<FAST_FINALIZE_CERT) ));
    s->slots[ n->label.slot ].canonical       = CANONICAL_BLOCK;
    s->slots[ n->label.slot ].canonical_block = block_id( n->label );
    if( (!s->canonical_final) & direct ) s->canonical_final = n->label.slot;
    for( ulong slot=n->parent.slot+1UL; slot<n->label.slot; slot++ ) s->slots[ slot ].canonical = CANONICAL_SKIP;
    if( FD_UNLIKELY( n->parent.slot && !node_find( s, n->parent ) ) ) FD_LOG_ERR(( "canonical block in slot %lu cites a parent with no actions", n->label.slot ));
  }
  s->slots[ 0 ].canonical = CANONICAL_BLOCK;
}

static uchar *
file_read( char const * path,
           ulong *      size ) {
  int fd = open( path, O_RDONLY );
  if( FD_UNLIKELY( fd<0 ) ) FD_LOG_ERR(( "open(%s) failed", path ));
  struct stat st;
  FD_TEST( !fstat( fd, &st ) );
  if( FD_UNLIKELY( !S_ISREG( st.st_mode ) ) ) FD_LOG_ERR(( "%s is not a regular file", path ));
  FD_TEST( st.st_size>=0L );
  *size = (ulong)st.st_size;
  if( FD_UNLIKELY( *size>memory.data_max ) ) FD_LOG_ERR(( "%s exceeds preallocated input capacity", path ));
  ulong read_sz;
  FD_TEST( !fd_io_read( fd, memory.data, *size, *size, &read_sz ) );
  FD_TEST( read_sz==*size );
  FD_TEST( !close( fd ) );
  return memory.data;
}

static void *
memory_new( ulong cnt,
            ulong ele_sz ) {
  FD_TEST( ele_sz && cnt<=ULONG_MAX/ele_sz );
  ulong sz = fd_ulong_max( cnt*ele_sz, 1UL );
  void * p = mmap( NULL, sz, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0 );
  FD_TEST( p!=MAP_FAILED );
  return p;
}

/* Read inputs once to size every buffer.  The node count used to reserve
   pool/votor storage is an upper bound; scenario_run still initializes
   them with each scenario's actual capacity.  Mappings are demand-paged,
   so workers only touch the portions used by their scenarios. */

static void
memory_init( char ** paths,
             ulong   path_cnt ) {
  memory.data_max = 1UL;
  for( ulong i=0UL; i<path_cnt; i++ ) {
    struct stat st;
    if( FD_UNLIKELY( stat( paths[i], &st ) ) ) FD_LOG_ERR(( "stat(%s) failed", paths[i] ));
    if( FD_UNLIKELY( !S_ISREG( st.st_mode ) ) ) FD_LOG_ERR(( "%s is not a regular file", paths[i] ));
    FD_TEST( st.st_size>=0L );
    memory.data_max = fd_ulong_max( memory.data_max, (ulong)st.st_size );
  }
  memory.data = memory_new( memory.data_max, 1UL );

  for( ulong i=0UL; i<path_cnt; i++ ) {
    ulong size;
    uchar * data = file_read( paths[i], &size );
    scenario_t s = { .slot_cnt = 1UL, .width = 1UL };
    actions_parse( &s, data, size );
    FD_TEST( s.slot_cnt<=ULONG_MAX/s.width );
    ulong node_max = s.slot_cnt*s.width;
    ulong node_cnt = fd_ulong_min( s.action_cnt, node_max );
    FD_TEST( (s.vote_slot_cnt<=ULONG_MAX-AG_REWARD_SLOT_DELTA) & (node_cnt<=ULONG_MAX-2UL) );
    ulong pool_slot_max = fd_ulong_max( s.vote_slot_cnt+AG_REWARD_SLOT_DELTA, node_cnt+2UL );
    memory.action_max    = fd_ulong_max( memory.action_max,    s.action_cnt    );
    memory.node_max      = fd_ulong_max( memory.node_max,      node_max        );
    memory.vote_slot_max = fd_ulong_max( memory.vote_slot_max, s.vote_slot_cnt );
    memory.pool_slot_max = fd_ulong_max( memory.pool_slot_max, pool_slot_max   );
  }

  memory.pool_sz  = ag_pool_footprint ( memory.pool_slot_max );
  memory.votor_sz = ag_votor_footprint( memory.pool_slot_max );
  FD_TEST( (!!memory.pool_sz) & (!!memory.votor_sz) );
  memory.actions = memory_new( memory.action_max,    sizeof(action_t) );
  memory.nodes   = memory_new( memory.node_max,      sizeof(node_t)   );
  memory.slots   = memory_new( memory.vote_slot_max, sizeof(slot_t)   );
  memory.pool    = memory_new( memory.pool_sz,       1UL );
  memory.votor   = memory_new( memory.votor_sz,      1UL );
  memory.slot_initialized = memory_new( memory.pool_slot_max, sizeof(uchar) );
  FD_TEST( fd_ulong_is_aligned( (ulong)memory.pool,  ag_pool_align()  ) );
  FD_TEST( fd_ulong_is_aligned( (ulong)memory.votor, ag_votor_align() ) );
}

static void
memory_fini( void ) {
  FD_TEST( !munmap( memory.slot_initialized, memory.pool_slot_max*sizeof(uchar) ) );
  FD_TEST( !munmap( memory.votor,   memory.votor_sz ) );
  FD_TEST( !munmap( memory.pool,    memory.pool_sz  ) );
  FD_TEST( !munmap( memory.slots,   memory.vote_slot_max*sizeof(slot_t) ) );
  FD_TEST( !munmap( memory.nodes,   memory.node_max*sizeof(node_t) ) );
  FD_TEST( !munmap( memory.actions, fd_ulong_max( memory.action_max*sizeof(action_t), 1UL ) ) );
  FD_TEST( !munmap( memory.data,    memory.data_max ) );
}

/* Parses a scenario and derives its nodes, canonical chain and vote bounds. */

static void
scenario_load( scenario_t * s,
               char const * path ) {
  ulong   size;
  uchar * data = file_read( path, &size );
  memset( s, 0, sizeof(scenario_t) );
  s->actions  = memory.actions;
  s->nodes    = memory.nodes;
  s->slots    = memory.slots;
  s->slot_cnt = 1UL;
  s->width    = 1UL;
  actions_parse( s, data, size );
  nodes_build( s );

  if( FD_UNLIKELY( s->vote_slot_cnt>memory.vote_slot_max ) ) FD_LOG_ERR(( "scenario exceeds preallocated slot capacity" ));
  memset( s->slots, 0, s->vote_slot_cnt*sizeof(slot_t) );
  s->slots[ 0 ].voted_notar = 1; /* the root, as ag_votor_init */
  canonical_build( s );
}

/* Invariants */

/* Notar or skip at most once per slot, notar only for live replayed blocks, final only for the canonical one. */

static void
check_vote( scenario_t *            s,
            ag_event_vote_t const * event ) {
  ag_vote_t const * vote = &event->vote;
  FD_TEST( ag_vote_rank( vote )==0UL ); /* required by test_slot_state_null */
  ulong             slot = ag_vote_slot( vote );
  FD_TEST( slot<s->vote_slot_cnt );
  slot_t * st = &s->slots[ slot ];
  switch( vote->kind ) {
  case AG_VOTE_KIND_NOTAR: {
    if( FD_UNLIKELY( st->voted_skip  ) ) FD_LOG_CRIT(( "INVARIANT: voted notar and skip in slot %lu", slot ));
    if( FD_UNLIKELY( st->voted_notar ) ) FD_LOG_CRIT(( "INVARIANT: voted notar twice in slot %lu", slot ));
    node_t const * n = node_of_block( s, slot, vote->notar.block_hash );
    if( FD_UNLIKELY( !n || ( (!n->replayed) | (!!n->dead) ) ) ) FD_LOG_CRIT(( "INVARIANT: voted notar in slot %lu for a block replay did not complete or found dead", slot ));
    st->voted_notar = 1;
    memcpy( st->voted_notar_hash, vote->notar.block_hash, sizeof(ag_block_hash_t) );
    break;
  }
  case AG_VOTE_KIND_SKIP:
    if( FD_UNLIKELY( st->voted_notar ) ) FD_LOG_CRIT(( "INVARIANT: voted notar and skip in slot %lu", slot ));
    if( FD_UNLIKELY( st->voted_skip  ) ) FD_LOG_CRIT(( "INVARIANT: voted skip twice in slot %lu", slot ));
    st->voted_skip = 1;
    break;
  case AG_VOTE_KIND_FINAL:
    if( FD_UNLIKELY( ( (st->canonical!=CANONICAL_BLOCK) | (!st->voted_notar) ) ||
                    memcmp( st->voted_notar_hash, st->canonical_block.hash, sizeof(ag_block_hash_t) ) ) ) {
      FD_LOG_CRIT(( "INVARIANT: voted final in slot %lu without voting notar for its canonical block", slot ));
    }
    st->voted_final = 1;
    break;
  default:
    break;
  }
}

/* Whether a block the tracker holds as finalized descends from block
   through the parent links replay gave the pool. */

static int
finalized_descendant( scenario_t const *            s,
                      ag_finality_tracker_t const * tracker,
                      ag_block_id_t const *         block ) {
  for( ulong later=block->slot+1UL; later<s->slot_cnt; later++ ) {
    ag_block_hash_t hash;
    if( ag_finality_tracker_status( tracker, later, hash )!=AG_FINALIZATION_STATUS_FINALIZED ) continue;
    ag_block_id_t id = ag_block_id( later, hash );
    while( id.slot>block->slot ) {
      node_t const * n = node_of_block( s, id.slot, id.hash );
      if( !n || !n->replayed ) break;
      id = n->replayed_parent;
    }
    if( ag_block_id_eq( &id, block ) ) return 1;
  }
  return 0;
}

/* Finalized blocks have a notar and final cert or a fast final cert; implicitly finalized ones a finalized descendant. */

static void
check_finality( scenario_t const * s,
                ag_pool_t const *  pool ) {
  ag_finality_tracker_t const * tracker = pool->finality_tracker;
  for( ulong slot=1UL; slot<s->slot_cnt; slot++ ) {
    ag_block_hash_t hash;
    switch( ag_finality_tracker_status( tracker, slot, hash ) ) {
    case AG_FINALIZATION_STATUS_FINALIZED: {
      ag_slot_state_t const * state      = ag_pool_slot_state( pool, slot );
      int                     final      = state && state->certs.finalize.slot!=ULONG_MAX;
      int                     notar      = state && state->certs.notar.slot!=ULONG_MAX         && !memcmp( state->certs.notar.block_hash,         hash, sizeof(ag_block_hash_t) );
      int                     fast_final = state && state->certs.fast_finalize.slot!=ULONG_MAX && !memcmp( state->certs.fast_finalize.block_hash, hash, sizeof(ag_block_hash_t) );
      if( FD_UNLIKELY( (!( final & notar )) & (!fast_final) ) ) FD_LOG_CRIT(( "INVARIANT: finalized slot %lu without a final and notar cert or a fast final cert", slot ));
      break;
    }
    case AG_FINALIZATION_STATUS_IMPLICITLY_FINALIZED: {
      ag_block_id_t block = ag_block_id( slot, hash );
      if( FD_UNLIKELY( !finalized_descendant( s, tracker, &block ) ) ) FD_LOG_CRIT(( "INVARIANT: implicitly finalized slot %lu without a finalized descendant linked to it", slot ));
      break;
    }
    default:
      break;
    }
  }
}

/* Only canonical blocks are finalized, and only slots the canonical chain skips are skipped. */

static void
check_canonical( scenario_t const * s,
                 ag_pool_t const *  pool ) {
  ag_finality_tracker_t const * tracker = pool->finality_tracker;
  for( ulong slot=1UL; slot<s->slot_cnt; slot++ ) {
    ag_block_hash_t hash;
    int             kind = s->slots[ slot ].canonical;
    switch( ag_finality_tracker_status( tracker, slot, hash ) ) {
    case AG_FINALIZATION_STATUS_FINALIZED:
    case AG_FINALIZATION_STATUS_IMPLICITLY_FINALIZED:
      if( FD_UNLIKELY( kind!=CANONICAL_BLOCK || memcmp( hash, s->slots[ slot ].canonical_block.hash, sizeof(ag_block_hash_t) ) ) ) {
        FD_LOG_CRIT(( "INVARIANT: finalized a block off the canonical chain in slot %lu", slot ));
      }
      break;
    case AG_FINALIZATION_STATUS_IMPLICITLY_SKIPPED:
      if( FD_UNLIKELY( kind!=CANONICAL_SKIP ) ) FD_LOG_CRIT(( "INVARIANT: skipped slot %lu, which the canonical chain does not skip", slot ));
      break;
    default:
      break;
    }
  }
}

/* Shuttle events between pool and votor, as the votor tile does, until
   both are quiet, then check finality. */

static void
pump( scenario_t * s,
      ag_pool_t *  pool,
      ag_votor_t * votor,
      long         now ) {
  for( int progress=1; progress; ) {
    progress = 0;

    ag_event_pool_t pool_event;
    if( ag_pool_poll_pool_event( pool, &pool_event ) ) {
      ag_votor_handle_pool_event( votor, &pool_event, now );
      progress = 1;
    }

    ag_event_repair_t repair_event;
    if( ag_pool_poll_repair_event( pool, &repair_event ) ) progress = 1;

    ag_event_timeout_t timeout_event;
    if( ag_votor_poll_timeout_event( votor, now, &timeout_event ) ) {
      ag_votor_handle_timeout_event( votor, &timeout_event );
      progress = 1;
    }

    ag_event_vote_t vote_event;
    if( ag_votor_poll_vote_event( votor, &vote_event ) ) {
      check_vote( s, &vote_event );
      uchar quorum_reached;
      ag_pool_add_vote( pool, &vote_event.vote, bad, &quorum_reached );
      progress = 1;
    }

    ag_event_cert_t cert_event;
    if( ag_votor_poll_cert_event( votor, &cert_event ) ) {
      ag_pool_add_cert( pool, &cert_event.cert, bad );
      progress = 1;
    }
  }
  check_finality( s, pool );
  check_canonical( s, pool );
}

/* Runs the actions against a fresh pool and votor, then checks the finalized slot. */

static void
scenario_run( scenario_t * s ) {
  /* The pool holds slots up to slot_max-AG_REWARD_SLOT_DELTA past the
     root, and its event queues hold slot_max events. */
  ulong slot_max = fd_ulong_max( s->vote_slot_cnt+AG_REWARD_SLOT_DELTA, s->node_cnt+2UL );
  FD_TEST( slot_max<=memory.pool_slot_max );

  /* Pool metadata follows the slot array.  A smaller capacity can overwrite
     previously initialized slots beyond its end; invalidate their markers. */
  memset( memory.slot_initialized+slot_max, 0, memory.pool_slot_max-slot_max );
  ag_pool_t *  pool  = ag_pool_join ( ag_pool_new ( memory.pool,  slot_max, 42UL ) );
  ag_votor_t * votor = ag_votor_join( ag_votor_new( memory.votor, slot_max, 42UL ) );
  FD_TEST( (!!pool) & (!!votor) );
  memory.slot_pool = pool->slot_states->pool;
  ag_pool_init          ( pool, 0UL );
  ag_pool_advance_epoch ( pool, &epoch_info, 0UL, 0UL );
  ag_votor_init         ( votor, 0UL, 0L, NS_PER_SLOT, SHRED_VERSION, fake_sign_fn, NULL );
  ag_votor_advance_epoch( votor, NS_PER_SLOT, 0UL, 0UL );

  long now = 0L;
  for( ulong i=0UL; i<s->action_cnt; i++ ) {
    action_t const * a = &s->actions[i];
    switch( a->kind ) {
    case NOTARIZE_CERT:
    case FINALIZE_CERT:
    case NOTAR_FALLBACK_CERT:
    case FAST_FINALIZE_CERT:
    case SKIP_CERT: {
      ag_cert_t c = cert( a->kind, a->label );
      ag_pool_add_cert( pool, &c, bad );
      break;
    }
    case REPLAY_ARRIVES:
      /* The votor only receives completed replay events. */
      break;
    case REPLAY_COMPLETE: {
      ag_block_id_t id     = block_id( a->label );
      ag_block_id_t parent = block_id( a->parent );
      if( ag_pool_add_block( pool, &id, &parent, bad )==AG_POOL_ERR_SLOT_OUT_OF_BOUNDS ) break;
      node_t * n          = node_find( s, a->label );
      n->replayed         = 1;
      n->replayed_parent  = parent;
      ag_event_replay_t completed = { .slot = id.slot, .block_info = { .parent = parent } };
      memcpy( completed.block_info.hash, id.hash, sizeof(ag_block_hash_t) );
      ag_votor_handle_replay_event( votor, &completed );
      break;
    }
    case REPLAY_DEAD:
      /* Dead blocks affect the vote invariant, but do not immediately
         trigger skip votes in the current votor. */
      node_find( s, a->label )->dead = 1;
      break;
    case CLOCK:
      now += (long)a->ms*1000000L;
      break;
    }
    pump( s, pool, votor, now );
  }
  pump( s, pool, votor, now+NS_EVERY_TIMEOUT );

  ulong         finalized_slot = ag_pool_finalized_slot( pool );
  uchar const * finalized_hash = ag_pool_finalized_block_hash( pool );
  if( FD_UNLIKELY( finalized_slot!=s->canonical_final ||
                  ( finalized_slot && ( !finalized_hash || memcmp( finalized_hash, s->slots[ finalized_slot ].canonical_block.hash, sizeof(ag_block_hash_t) ) ) ) ) ) {
    FD_LOG_CRIT(( "INVARIANT: finalized slot %lu, not canonical slot %lu", finalized_slot, s->canonical_final ));
  }

  ag_votor_delete( ag_votor_leave( votor ) );
  ag_pool_delete ( ag_pool_leave ( pool  ) );
}

/* Workers.  FD_TEST exits without a backtrace, so a worker logs one on
   exit.  It never exits on success: _exit skips atexit.  FD_LOG_CRIT
   aborts, and fd_log logs its own. */

static void
backtrace_on_exit( void ) {
  void * frames[ 128 ];
  fd_backtrace_log( frames, (ulong)backtrace( frames, 128 ) );
}

static void
worker( char ** paths,
        ulong   path_cnt,
        ulong   first,
        ulong   stride,
        ulong * current ) {
  atexit( backtrace_on_exit );
  fd_log_level_logfile_set( 4 ); /* ERR and up, the votor warns a lot */
  fd_log_level_stderr_set ( 4 );
  for( ulong i=first; i<path_cnt; i+=stride ) {
    *current = i;
    scenario_t s;
    scenario_load( &s, paths[i] );
    scenario_run( &s );
  }
  _exit( 0 );
}

/* Forks --jobs workers over the inputs and prints the first failing input. */

int
main( int     argc,
      char ** argv ) {
  fd_boot( &argc, &argv );
  ulong jobs = fd_env_strip_cmdline_ulong( &argc, &argv, "--jobs", NULL, (ulong)sysconf( _SC_NPROCESSORS_ONLN ) );

  /* The unit-test runner supplies workspace options; this test maps its own storage. */
  fd_env_strip_cmdline_cstr( &argc, &argv, "--page-sz",  NULL, NULL );
  fd_env_strip_cmdline_cstr( &argc, &argv, "--page-cnt", NULL, NULL );
  fd_env_strip_cmdline_cstr( &argc, &argv, "--numa-idx", NULL, NULL );

  glob_t g = { 0 };
  int input_cnt = argc>1 ? argc-1 : 1;
  for( int i=0; i<input_cnt; i++ ) {
    /* A directory runs every entry in it */
    char         pattern[ PATH_MAX ];
    char const * arg = argc>1 ? argv[i+1] : "src/choreo/votor/scenarios/*.json";
    struct stat  st;
    if( !stat( arg, &st ) && S_ISDIR( st.st_mode ) ) {
      FD_TEST( fd_cstr_printf_check( pattern, sizeof(pattern), NULL, "%s/*", arg ) );
      arg = pattern;
    }
    if( FD_UNLIKELY( glob( arg, i ? GLOB_APPEND : 0, NULL, &g ) ) ) FD_LOG_ERR(( "no input matches %s", arg ));
  }
  if( FD_UNLIKELY( !g.gl_pathc ) ) FD_LOG_ERR(( "usage: %s [--jobs N] [<file|dir|pattern>...]", argv[0] ));
  jobs = fd_ulong_max( fd_ulong_min( jobs, g.gl_pathc ), 1UL );

  cluster_init();
  memory_init( g.gl_pathv, g.gl_pathc );

  ulong * current = mmap( NULL, jobs*sizeof(ulong), PROT_READ|PROT_WRITE, MAP_SHARED|MAP_ANONYMOUS, -1, 0 );
  pid_t * pids    = memory_new( jobs, sizeof(pid_t) );
  FD_TEST( (current!=MAP_FAILED) & (!!pids) );
  for( ulong w=0UL; w<jobs; w++ ) {
    pids[w] = fork();
    FD_TEST( pids[w]>=0 );
    if( !pids[w] ) worker( g.gl_pathv, g.gl_pathc, w, jobs, &current[w] );
  }

  int failed = 0;
  for( ulong left=jobs; (!!left) & (!failed); left-- ) {
    int   status;
    pid_t pid = wait( &status );
    FD_TEST( pid>0 );
    failed = !WIFEXITED( status ) || WEXITSTATUS( status );
    for( ulong w=0UL; (!!failed) & (w<jobs); w++ ) {
      if( pids[w]!=pid ) { kill( pids[w], SIGKILL ); continue; }
      ulong   size;
      uchar * data = file_read( g.gl_pathv[ current[w] ], &size );
      fprintf( stderr, "\nfailing input: %s\n%.*s\n", g.gl_pathv[ current[w] ], (int)size, (char const *)data );
    }
  }

  if( FD_LIKELY( !failed ) ) FD_LOG_NOTICE(( "pass: %lu scenarios", g.gl_pathc ));
  FD_TEST( !munmap( pids, jobs*sizeof(pid_t) ) );
  FD_TEST( !munmap( current, jobs*sizeof(ulong) ) );
  memory_fini();
  globfree( &g );
  fd_halt();
  return failed;
}
