#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include "fd_forest.h"
#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"

#include <stdlib.h>

#define FUZZ_ELE_MAX       (8UL)
#define FUZZ_MAX_OPS       (96UL)
#define FUZZ_SLOT_BASE     (1000UL)
#define FUZZ_SLOT_SPREAD   (64UL)
#define FUZZ_FEC_SET_MAX   (3UL)
#define FUZZ_ACTOR_CNT     (4U)
#define FUZZ_OP_KIND_CNT   (9U)

#define FUZZ_ACTOR_TURBINE (0U)
#define FUZZ_ACTOR_REPAIR  (1U)
#define FUZZ_ACTOR_TOWER   (2U)
#define FUZZ_ACTOR_STORE   (3U)

typedef struct {
  uchar const * data;
  ulong         data_sz;
  ulong         data_off;
} fuzz_cursor_t;

typedef enum {
  FUZZ_OP_DATA_SHRED = 0,
  FUZZ_OP_FEC,
  FUZZ_OP_CODE_SHRED,
  FUZZ_OP_CONFIRM,
  FUZZ_OP_PUBLISH,
  FUZZ_OP_CLEAR,
  FUZZ_OP_ITER,
  FUZZ_OP_FILL_POOL,
  FUZZ_OP_VALIDATE,
} fuzz_op_kind_t;

typedef struct {
  fuzz_op_kind_t kind;
  uchar          actor;
  uchar          arg0;
  uchar          arg1;
  ushort         arg2;
  uint           raw;
} fuzz_op_t;

typedef struct {
  fuzz_op_t ops[ FUZZ_MAX_OPS ];
  ulong     op_cnt;
} fuzz_program_t;

typedef struct {
  fd_forest_t * forest;
  ulong         next_slot;
  ulong         last_root;
} fuzz_env_t;

static fd_wksp_t * g_wksp;

static uchar
fuzz_fallback_u8( fuzz_cursor_t const * cur ) {
  ulong h = fd_ulong_hash( cur->data_off ^ (cur->data_sz<<1) ^
                           0x9e3779b97f4a7c15UL );
  return (uchar)(h>>56);
}

static uchar
fuzz_u8( fuzz_cursor_t * cur ) {
  if( FD_LIKELY( cur->data_off < cur->data_sz ) ) {
    return cur->data[ cur->data_off++ ];
  }
  cur->data_off++;
  return fuzz_fallback_u8( cur );
}

static uint
fuzz_u32( fuzz_cursor_t * cur ) {
  uint v = (uint)fuzz_u8( cur );
  v |= (uint)fuzz_u8( cur ) <<  8U;
  v |= (uint)fuzz_u8( cur ) << 16U;
  v |= (uint)fuzz_u8( cur ) << 24U;
  return v;
}

static void
fuzz_decode_program( fuzz_cursor_t *  cur,
                     fuzz_program_t * prog ) {
  prog->op_cnt = 0UL;

  while( cur->data_off < cur->data_sz && prog->op_cnt < FUZZ_MAX_OPS ) {
    fuzz_op_t * op = &prog->ops[ prog->op_cnt++ ];
    op->actor = (uchar)( fuzz_u8( cur ) % FUZZ_ACTOR_CNT );
    op->kind  = (fuzz_op_kind_t)( fuzz_u8( cur ) % FUZZ_OP_KIND_CNT );
    op->arg0  = fuzz_u8( cur );
    op->arg1  = fuzz_u8( cur );
    op->arg2  = (ushort)( ((ushort)fuzz_u8( cur ) << 8U) |
                           (ushort)fuzz_u8( cur )       );
    op->raw   = fuzz_u32( cur );
  }

  if( prog->op_cnt < FUZZ_MAX_OPS ) {
    prog->ops[ prog->op_cnt++ ] = (fuzz_op_t) {
      .kind  = FUZZ_OP_VALIDATE,
      .actor = FUZZ_ACTOR_STORE,
    };
  }
}

static void
fuzz_hash( fd_hash_t * out,
           ulong       tag,
           ulong       slot,
           uint        fec_set_idx,
           uint        version ) {
  ulong seed = fd_ulong_hash( tag ^ (slot<<1) ^
                              ((ulong)fec_set_idx<<33) ^
                              ((ulong)version<<48) );
  for( ulong i=0UL; i<4UL; i++ ) {
    out->ul[ i ] = fd_ulong_hash( seed + 0x9e3779b97f4a7c15UL*(i+1UL) );
  }
  if( FD_UNLIKELY( !out->ul[0] && !out->ul[1] &&
                   !out->ul[2] && !out->ul[3] ) ) out->ul[0] = 1UL;
}

static ulong
fuzz_collect_slots( fd_forest_t * forest,
                    ulong *       slots,
                    ulong         slots_max,
                    int           above_root,
                    int           below_slot,
                    ulong         slot_bound ) {
  fd_forest_blk_t * pool = fd_forest_pool( forest );
  ulong             root = fd_forest_root_slot( forest );
  ulong             cnt  = 0UL;

# define COLLECT_FROM_MAP( map_name ) do {                                          \
    map_name##_t * map = map_name( forest );                                        \
    for( map_name##_iter_t iter = map_name##_iter_init( map, pool );                \
         !map_name##_iter_done( iter, map, pool );                                  \
         iter = map_name##_iter_next( iter, map, pool ) ) {                         \
      fd_forest_blk_t * ele = map_name##_iter_ele( iter, map, pool );               \
      if( above_root && ele->slot<=root ) continue;                                 \
      if( below_slot && ele->slot>=slot_bound ) continue;                           \
      if( cnt<slots_max ) slots[ cnt++ ] = ele->slot;                               \
    }                                                                               \
  } while(0)

  COLLECT_FROM_MAP( fd_forest_ancestry  );
  COLLECT_FROM_MAP( fd_forest_frontier  );
  COLLECT_FROM_MAP( fd_forest_subtrees  );
  COLLECT_FROM_MAP( fd_forest_orphaned  );

# undef COLLECT_FROM_MAP
  return cnt;
}

static ulong
fuzz_pick_live_slot( fd_forest_t * forest,
                     uchar         selector,
                     int           above_root ) {
  ulong slots[ FUZZ_ELE_MAX ];
  ulong cnt = fuzz_collect_slots( forest, slots, FUZZ_ELE_MAX,
                                  above_root, 0, ULONG_MAX );
  if( FD_UNLIKELY( !cnt ) ) return ULONG_MAX;
  return slots[ (ulong)selector % cnt ];
}

static ulong
fuzz_pick_parent_slot( fd_forest_t * forest,
                       ulong         slot,
                       uchar         selector ) {
  ulong root = fd_forest_root_slot( forest );
  if( FD_UNLIKELY( slot<=root+1UL ) ) return root;

  switch( selector % 5U ) {
    case 0U:
      return root;
    case 1U: {
      ulong slots[ FUZZ_ELE_MAX ];
      ulong cnt = fuzz_collect_slots( forest, slots, FUZZ_ELE_MAX,
                                      0, 1, slot );
      return cnt ? slots[ ((ulong)selector>>3) % cnt ] : root;
    }
    case 2U:
      return slot-1UL; /* Often absent, forming a repair orphan chain. */
    case 3U: {
      ulong span = slot-root-1UL;
      return root + 1UL + ((ulong)selector % span);
    }
    default:
      return fd_ulong_max( root, slot-2UL );
  }
}

static ulong
fuzz_alloc_slot( fuzz_env_t * env,
                 uchar        selector ) {
  ulong root = fd_forest_root_slot( env->forest );
  if( FD_UNLIKELY( env->next_slot<=root ) ) env->next_slot = root + 1UL;

  ulong slot = env->next_slot + ((ulong)selector % 4UL);
  env->next_slot = slot + 1UL;
  return slot;
}

static uint
fuzz_fec_set_idx( uchar selector ) {
  return (uint)( ((ulong)selector % FUZZ_FEC_SET_MAX) * FD_FEC_SHRED_CNT );
}

static uint
fuzz_pick_shred_idx( fd_forest_blk_t const * ele,
                     uint                    fec_set_idx,
                     uchar                   selector ) {
  uint shred_idx = fec_set_idx + (uint)( selector % FD_FEC_SHRED_CNT );
  if( FD_LIKELY( ele && ele->complete_idx!=UINT_MAX ) ) {
    if( FD_UNLIKELY( fec_set_idx > ele->complete_idx ) ) return ele->complete_idx;
    shred_idx = fd_uint_min( shred_idx, ele->complete_idx );
  }
  return shred_idx;
}

static int
fuzz_ref_in_list( fd_forest_reqslist_t const * list,
                  fd_forest_ref_t const *      pool,
                  ulong                        idx ) {
  for( fd_forest_reqslist_iter_t iter = fd_forest_reqslist_iter_fwd_init( list, pool );
       !fd_forest_reqslist_iter_done( iter, list, pool );
       iter = fd_forest_reqslist_iter_fwd_next( iter, list, pool ) ) {
    fd_forest_ref_t const * ele = fd_forest_reqslist_iter_ele_const( iter, list, pool );
    if( ele->idx==idx ) return 1;
  }
  return 0;
}

static int
fuzz_cons_ref_in_list( fd_forest_conslist_t const * list,
                       fd_forest_ref_t const *      pool,
                       ulong                        idx ) {
  for( fd_forest_conslist_iter_t iter = fd_forest_conslist_iter_fwd_init( list, pool );
       !fd_forest_conslist_iter_done( iter, list, pool );
       iter = fd_forest_conslist_iter_fwd_next( iter, list, pool ) ) {
    fd_forest_ref_t const * ele = fd_forest_conslist_iter_ele_const( iter, list, pool );
    if( ele->idx==idx ) return 1;
  }
  return 0;
}

static void
fuzz_validate_ref_maps( fd_forest_t const * forest ) {
  fd_forest_blk_t const * pool = fd_forest_pool_const( forest );

  fd_forest_ref_t const * conspool = fd_forest_conspool_const( forest );
  fd_forest_consumed_t const * consumed = fd_forest_consumed_const( forest );
  fd_forest_conslist_t const * conslist = fd_forest_conslist_const( forest );
  ulong consumed_list_cnt = 0UL;

  for( fd_forest_conslist_iter_t iter = fd_forest_conslist_iter_fwd_init( conslist, conspool );
       !fd_forest_conslist_iter_done( iter, conslist, conspool );
       iter = fd_forest_conslist_iter_fwd_next( iter, conslist, conspool ) ) {
    fd_forest_ref_t const * ele = fd_forest_conslist_iter_ele_const( iter, conslist, conspool );
    consumed_list_cnt++;
    FD_TEST( fd_forest_pool_ele_const( pool, ele->idx ) );
    FD_TEST( fd_forest_consumed_ele_query_const( consumed, &ele->idx, NULL, conspool ) );
  }

  ulong consumed_map_cnt = 0UL;
  for( fd_forest_consumed_iter_t iter = fd_forest_consumed_iter_init( consumed, conspool );
       !fd_forest_consumed_iter_done( iter, consumed, conspool );
       iter = fd_forest_consumed_iter_next( iter, consumed, conspool ) ) {
    fd_forest_ref_t const * ele = fd_forest_consumed_iter_ele_const( iter, consumed, conspool );
    consumed_map_cnt++;
    FD_TEST( fuzz_cons_ref_in_list( conslist, conspool, ele->idx ) );
  }
  FD_TEST( consumed_list_cnt==consumed_map_cnt );

  fd_forest_ref_t const * reqspool = fd_forest_reqspool_const( forest );
  fd_forest_requests_t const * requests = fd_forest_requests_const( forest );
  fd_forest_reqslist_t const * reqslist = fd_forest_reqslist_const( forest );
  fd_forest_requests_t const * orphreqs = fd_forest_orphreqs_const( forest );
  fd_forest_reqslist_t const * orphlist = fd_forest_orphlist_const( forest );

# define CHECK_REQ_PAIR( map, list ) do {                                                \
    ulong list_cnt = 0UL;                                                                \
    for( fd_forest_reqslist_iter_t iter = fd_forest_reqslist_iter_fwd_init( (list), reqspool ); \
         !fd_forest_reqslist_iter_done( iter, (list), reqspool );                        \
         iter = fd_forest_reqslist_iter_fwd_next( iter, (list), reqspool ) ) {           \
      fd_forest_ref_t const * ele = fd_forest_reqslist_iter_ele_const( iter, (list), reqspool ); \
      list_cnt++;                                                                        \
      FD_TEST( fd_forest_pool_ele_const( pool, ele->idx ) );                             \
      FD_TEST( fd_forest_requests_ele_query_const( (map), &ele->idx, NULL, reqspool ) ); \
    }                                                                                    \
    ulong map_cnt = 0UL;                                                                 \
    for( fd_forest_requests_iter_t iter = fd_forest_requests_iter_init( (map), reqspool ); \
         !fd_forest_requests_iter_done( iter, (map), reqspool );                         \
         iter = fd_forest_requests_iter_next( iter, (map), reqspool ) ) {                \
      fd_forest_ref_t const * ele = fd_forest_requests_iter_ele_const( iter, (map), reqspool ); \
      map_cnt++;                                                                         \
      FD_TEST( fuzz_ref_in_list( (list), reqspool, ele->idx ) );                         \
    }                                                                                    \
    FD_TEST( list_cnt==map_cnt );                                                        \
  } while(0)

  CHECK_REQ_PAIR( requests, reqslist );
  CHECK_REQ_PAIR( orphreqs, orphlist );

# undef CHECK_REQ_PAIR

  for( fd_forest_requests_iter_t iter = fd_forest_requests_iter_init( requests, reqspool );
       !fd_forest_requests_iter_done( iter, requests, reqspool );
       iter = fd_forest_requests_iter_next( iter, requests, reqspool ) ) {
    fd_forest_ref_t const * ele = fd_forest_requests_iter_ele_const( iter, requests, reqspool );
    FD_TEST( !fd_forest_requests_ele_query_const( orphreqs, &ele->idx, NULL, reqspool ) );
  }
}

static void
fuzz_validate( fuzz_env_t * env ) {
  ulong root = fd_forest_root_slot( env->forest );
  FD_TEST( root!=ULONG_MAX );
  FD_TEST( root>=env->last_root );
  env->last_root = root;

  FD_TEST( !fd_forest_verify( env->forest ) );
  fuzz_validate_ref_maps( env->forest );
}

static fd_forest_blk_t *
fuzz_insert_block( fuzz_env_t * env,
                   ulong        slot,
                   ulong        parent_slot,
                   ulong *      evicted ) {
  if( FD_UNLIKELY( slot<=fd_forest_root_slot( env->forest ) ) ) return NULL;

  *evicted = ULONG_MAX;
  fd_forest_blk_t * blk = fd_forest_blk_insert( env->forest, slot, parent_slot, evicted );
  if( FD_UNLIKELY( *evicted!=ULONG_MAX ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( !blk ) ) FD_FUZZ_MUST_BE_COVERED;
  return blk;
}

static fd_forest_blk_t *
fuzz_prepare_block( fuzz_env_t * env,
                    fuzz_op_t const * op,
                    ulong *           slot,
                    ulong *           parent_slot,
                    ulong *           evicted ) {
  ulong live = fuzz_pick_live_slot( env->forest, op->arg0, 1 );
  if( FD_UNLIKELY( live!=ULONG_MAX && (op->arg1 & 1U) ) ) {
    fd_forest_blk_t * ele = fd_forest_query( env->forest, live );
    if( FD_LIKELY( ele ) ) {
      *slot = live;
      *parent_slot = ele->parent_slot==ULONG_MAX ?
                     fd_forest_root_slot( env->forest ) : ele->parent_slot;
      *evicted = ULONG_MAX;
      return ele;
    }
  }

  *slot = fuzz_alloc_slot( env, (uchar)(op->arg0 ^ (uchar)op->arg2) );
  *parent_slot = fuzz_pick_parent_slot( env->forest, *slot, op->arg1 );
  return fuzz_insert_block( env, *slot, *parent_slot, evicted );
}

static void
fuzz_op_data_shred( fuzz_env_t * env,
                    fuzz_op_t const * op ) {
  ulong slot;
  ulong parent_slot;
  ulong evicted;
  fd_forest_blk_t * ele = fuzz_prepare_block( env, op, &slot, &parent_slot, &evicted );
  if( FD_UNLIKELY( !ele ) ) return;

  uint fec_set_idx = fuzz_fec_set_idx( op->arg1 );
  if( FD_LIKELY( ele->complete_idx!=UINT_MAX && fec_set_idx > ele->complete_idx ) )
    fec_set_idx = (ele->complete_idx / FD_FEC_SHRED_CNT) * FD_FEC_SHRED_CNT;

  uint shred_idx = fuzz_pick_shred_idx( ele, fec_set_idx, op->arg0 );
  int  complete    = !!(op->arg2 & 1U);
  if( FD_LIKELY( complete ) ) shred_idx = fd_uint_min( shred_idx, fec_set_idx + FD_FEC_SHRED_CNT - 1U );
  if( FD_LIKELY( ele->complete_idx!=UINT_MAX ) ) complete = (shred_idx==ele->complete_idx);

  fd_hash_t mr[1];
  fd_hash_t cmr[1];
  fuzz_hash( mr,  0xa11ceUL, slot, fec_set_idx, (uint)(op->raw & 3U) );
  fuzz_hash( cmr, 0xb0bUL,   slot, fec_set_idx, (uint)((op->raw>>2) & 3U) );

  int src = op->actor==FUZZ_ACTOR_TURBINE ? SHRED_SRC_TURBINE :
            op->actor==FUZZ_ACTOR_REPAIR  ? SHRED_SRC_REPAIR  :
                                             SHRED_SRC_RECOVERED;
  fd_forest_blk_t * out =
    fd_forest_data_shred_insert( env->forest, slot, parent_slot, shred_idx,
                                 fec_set_idx, complete, (int)(op->arg2 & 63U),
                                 src, mr, cmr );
  if( FD_UNLIKELY( !out ) ) FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_op_fec( fuzz_env_t * env,
             fuzz_op_t const * op ) {
  ulong slot;
  ulong parent_slot;
  ulong evicted;
  fd_forest_blk_t * ele = fuzz_prepare_block( env, op, &slot, &parent_slot, &evicted );
  if( FD_UNLIKELY( !ele ) ) return;

  uint fec_set_idx = fuzz_fec_set_idx( op->arg0 );
  uint last_idx = fec_set_idx + (uint)(op->arg1 % FD_FEC_SHRED_CNT);
  if( FD_LIKELY( ele->complete_idx!=UINT_MAX ) ) {
    if( FD_UNLIKELY( fec_set_idx > ele->complete_idx ) ) {
      fec_set_idx = (ele->complete_idx / FD_FEC_SHRED_CNT) * FD_FEC_SHRED_CNT;
      last_idx    = ele->complete_idx;
    } else {
      last_idx = fd_uint_min( last_idx, ele->complete_idx );
    }
  }

  fd_hash_t mr[1];
  fd_hash_t cmr[1];
  fuzz_hash( mr,  0xcafeUL, slot, fec_set_idx, (uint)(op->raw & 3U) );
  fuzz_hash( cmr, 0xd00dUL, slot, fec_set_idx, (uint)((op->raw>>2) & 3U) );

  int slot_complete = !!(op->arg2 & 1U);
  fd_forest_blk_t * out =
    fd_forest_fec_insert( env->forest, slot, parent_slot, last_idx,
                          fec_set_idx, slot_complete, (int)(op->arg2 & 63U),
                          mr, cmr );
  if( FD_UNLIKELY( !out ) ) FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_op_code_shred( fuzz_env_t * env,
                    fuzz_op_t const * op ) {
  ulong slot = fuzz_pick_live_slot( env->forest, op->arg0, 1 );
  if( FD_UNLIKELY( slot==ULONG_MAX ) ) {
    ulong evicted;
    ulong new_slot = fuzz_alloc_slot( env, op->arg0 );
    ulong parent = fuzz_pick_parent_slot( env->forest, new_slot, op->arg1 );
    if( FD_UNLIKELY( !fuzz_insert_block( env, new_slot, parent, &evicted ) ) ) return;
    slot = new_slot;
  }

  uint shred_idx = (uint)(op->raw % (FD_FEC_SHRED_CNT*FUZZ_FEC_SET_MAX));
  fd_forest_blk_t * out = fd_forest_code_shred_insert( env->forest, slot, shred_idx );
  if( FD_UNLIKELY( !out ) ) FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_op_confirm( fuzz_env_t * env,
                 fuzz_op_t const * op ) {
  ulong slot = fuzz_pick_live_slot( env->forest, op->arg0, 1 );
  int absent = !!(op->arg1 & 1U) || slot==ULONG_MAX;

  if( FD_UNLIKELY( absent ) ) {
    if( FD_UNLIKELY( !fd_forest_pool_free( fd_forest_pool( env->forest ) ) ) ) return;
    slot = fuzz_alloc_slot( env, (uchar)(op->arg0 + 31U) );
    ulong evicted;
    fd_forest_blk_t * blk = fuzz_insert_block( env, slot, ULONG_MAX, &evicted );
    if( FD_UNLIKELY( !blk ) ) return;
    FD_FUZZ_MUST_BE_COVERED;

    fd_hash_t bid[1];
    fuzz_hash( bid, 0xf00dUL, slot, 0U, op->raw );
    blk->confirmed_bid = *bid; /* Mirrors repair tile duplicate-confirm handling. */
    return;
  }

  fd_forest_blk_t * blk = fd_forest_query( env->forest, slot );
  if( FD_UNLIKELY( !blk ) ) return;

  fd_hash_t bid[1];
  if( FD_LIKELY( blk->complete_idx!=UINT_MAX && !(op->arg1 & 2U) ) ) {
    *bid = blk->merkle_roots[ blk->complete_idx / FD_FEC_SHRED_CNT ].mr;
    if( FD_UNLIKELY( fd_hash_check_zero( bid ) ) )
      fuzz_hash( bid, 0xf00dUL, slot, 0U, op->raw );
  } else {
    fuzz_hash( bid, 0xf00dUL, slot, 0U, op->raw );
  }

  if( FD_UNLIKELY( blk->complete_idx==UINT_MAX ) ) {
    blk->confirmed_bid = *bid;
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  fd_forest_blk_t * bad = fd_forest_fec_chain_verify( env->forest, blk, bid );
  if( FD_UNLIKELY( bad ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    uint bad_idx = fd_forest_merkle_last_incorrect_idx( bad );
    if( FD_LIKELY( bad_idx!=UINT_MAX ) )
      fd_forest_fec_clear( env->forest, bad->slot, bad_idx, FD_FEC_SHRED_CNT-1U );
  }
}

static void
fuzz_op_publish( fuzz_env_t * env,
                 fuzz_op_t const * op ) {
  ulong old_root = fd_forest_root_slot( env->forest );
  ulong new_root = ULONG_MAX;

  if( FD_UNLIKELY( op->arg1 & 1U ) ) {
    if( FD_UNLIKELY( !fd_forest_pool_free( fd_forest_pool( env->forest ) ) ) ) return;
    new_root = fuzz_alloc_slot( env, (uchar)(op->arg0 + 17U) );
    if( FD_UNLIKELY( fd_forest_query( env->forest, new_root ) ) ) return;
    FD_FUZZ_MUST_BE_COVERED;
  } else {
    new_root = fuzz_pick_live_slot( env->forest, op->arg0, 1 );
    if( FD_UNLIKELY( new_root==ULONG_MAX ) ) {
      ulong evicted;
      new_root = fuzz_alloc_slot( env, op->arg0 );
      ulong parent = fuzz_pick_parent_slot( env->forest, new_root, 0U );
      if( FD_UNLIKELY( !fuzz_insert_block( env, new_root, parent, &evicted ) ) ) return;
    }
  }

  if( FD_UNLIKELY( new_root<=old_root ) ) return;
  fd_forest_blk_t const * root = fd_forest_publish( env->forest, new_root );
  FD_TEST( root );
  if( FD_LIKELY( new_root!=old_root ) ) FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_op_clear( fuzz_env_t * env,
               fuzz_op_t const * op ) {
  ulong slot = fuzz_pick_live_slot( env->forest, op->arg0, 1 );
  if( FD_UNLIKELY( slot==ULONG_MAX ) ) return;

  fd_forest_blk_t * ele = fd_forest_query( env->forest, slot );
  if( FD_UNLIKELY( !ele ) ) return;

  uint fec_set_idx = fuzz_fec_set_idx( op->arg1 );
  uint max_idx     = (uint)(op->arg2 % FD_FEC_SHRED_CNT);
  if( FD_LIKELY( ele->complete_idx!=UINT_MAX ) ) {
    if( FD_UNLIKELY( fec_set_idx > ele->complete_idx ) )
      fec_set_idx = (ele->complete_idx / FD_FEC_SHRED_CNT) * FD_FEC_SHRED_CNT;
    max_idx = fd_uint_min( max_idx, ele->complete_idx - fec_set_idx );
  }

  fd_forest_fec_clear( env->forest, slot, fec_set_idx, max_idx );
  FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_op_iter( fuzz_env_t * env,
              fuzz_op_t const * op ) {
  fd_forest_iter_t * iter = (op->arg0 & 1U) ? &env->forest->orphiter :
                                             &env->forest->iter;
  fd_forest_iter_next( iter, env->forest );
  if( FD_UNLIKELY( fd_forest_iter_done( iter, env->forest ) ) ) {
    FD_FUZZ_MUST_BE_COVERED;
  } else {
    fd_forest_blk_t const * ele =
      fd_forest_pool_ele_const( fd_forest_pool_const( env->forest ), iter->ele_idx );
    FD_TEST( ele );
    FD_TEST( fd_forest_query( env->forest, ele->slot ) );
    FD_FUZZ_MUST_BE_COVERED;
  }
}

static void
fuzz_op_fill_pool( fuzz_env_t * env,
                   fuzz_op_t const * op ) {
  ulong root = fd_forest_root_slot( env->forest );
  ulong base = root + 200UL + (ulong)(op->arg0 & 15U);

  for( ulong i=0UL; i<FUZZ_ELE_MAX+2UL; i++ ) {
    ulong slot = base + i*2UL;
    if( FD_UNLIKELY( slot<=fd_forest_root_slot( env->forest ) ) ) continue;
    if( FD_UNLIKELY( fd_forest_query( env->forest, slot ) ) ) continue;

    ulong parent_slot = slot - 1UL; /* Missing parent: creates an orphan leaf. */
    ulong evicted;
    int was_full = !fd_forest_pool_free( fd_forest_pool( env->forest ) );
    fd_forest_blk_t * blk = fuzz_insert_block( env, slot, parent_slot, &evicted );
    if( FD_UNLIKELY( was_full ) ) FD_FUZZ_MUST_BE_COVERED;
    if( FD_UNLIKELY( !blk ) ) break;
  }
}

static void
fuzz_execute_op( fuzz_env_t *       env,
                 fuzz_op_t const * op ) {
  switch( op->kind ) {
    case FUZZ_OP_DATA_SHRED:
      fuzz_op_data_shred( env, op );
      break;
    case FUZZ_OP_FEC:
      fuzz_op_fec( env, op );
      break;
    case FUZZ_OP_CODE_SHRED:
      fuzz_op_code_shred( env, op );
      break;
    case FUZZ_OP_CONFIRM:
      fuzz_op_confirm( env, op );
      break;
    case FUZZ_OP_PUBLISH:
      fuzz_op_publish( env, op );
      break;
    case FUZZ_OP_CLEAR:
      fuzz_op_clear( env, op );
      break;
    case FUZZ_OP_ITER:
      fuzz_op_iter( env, op );
      break;
    case FUZZ_OP_FILL_POOL:
      fuzz_op_fill_pool( env, op );
      break;
    case FUZZ_OP_VALIDATE:
      break;
    default:
      __builtin_unreachable();
  }

  fuzz_validate( env );
}

static void
fuzz_cleanup( void ) {
  if( FD_LIKELY( g_wksp ) ) {
    fd_wksp_delete_anonymous( g_wksp );
    g_wksp = NULL;
  }
}

int
LLVMFuzzerInitialize( int *    pargc,
                      char *** pargv ) {
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );

  fd_boot( pargc, pargv );

  char const * page_sz_cstr =
    fd_env_strip_cmdline_cstr ( pargc, pargv, "--page-sz",  NULL, "normal" );
  ulong page_cnt =
    fd_env_strip_cmdline_ulong( pargc, pargv, "--page-cnt", NULL, 1024UL );
  ulong numa_idx =
    fd_env_strip_cmdline_ulong( pargc, pargv, "--numa-idx", NULL,
                                fd_shmem_numa_idx( 0UL ) );

  g_wksp = fd_wksp_new_anonymous( fd_cstr_to_shmem_page_sz( page_sz_cstr ),
                                  page_cnt, fd_shmem_cpu_idx( numa_idx ),
                                  "forest_fuzz", 64UL );
  FD_TEST( g_wksp );

  atexit( fd_halt );
  atexit( fuzz_cleanup );
  fd_log_level_core_set( 4 );
  fd_log_level_stderr_set( 4 );
  fd_log_level_logfile_set( 4 );
  return 0;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         data_sz ) {
  fuzz_cursor_t cur = {
    .data     = data,
    .data_sz  = data_sz,
    .data_off = 0UL,
  };
  fuzz_program_t prog[1];
  fuzz_decode_program( &cur, prog );

  void * mem = fd_wksp_alloc_laddr( g_wksp, fd_forest_align(),
                                    fd_forest_footprint( FUZZ_ELE_MAX ), 1UL );
  FD_TEST( mem );

  fd_forest_t * forest =
    fd_forest_join( fd_forest_new( mem, FUZZ_ELE_MAX,
                                   42UL + fd_ulong_hash( data_sz ) ) );
  FD_TEST( forest );

  ulong root = FUZZ_SLOT_BASE + ( data_sz ? (ulong)(data[0] & 7U) : 0UL );
  fd_forest_init( forest, root );

  fuzz_env_t env = {
    .forest    = forest,
    .next_slot = root + 1UL + FUZZ_SLOT_SPREAD,
    .last_root = root,
  };
  fuzz_validate( &env );

  for( ulong i=0UL; i<prog->op_cnt; i++ ) {
    FD_FUZZ_MUST_BE_COVERED;
    fuzz_execute_op( &env, &prog->ops[ i ] );
  }

  fd_wksp_free_laddr( fd_forest_delete( fd_forest_leave( forest ) ) );
  return 0;
}
