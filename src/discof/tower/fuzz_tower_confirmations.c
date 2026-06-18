#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include <stdlib.h>
#include <string.h>

#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"

#define QUERY_TOWERS mock_query_towers
#define QUERY_VOTERS mock_query_voters
#define fd_tile_tower fd_tile_tower_fuzz_unused
#include "fd_tower_tile.c"
#undef fd_tile_tower
#undef QUERY_TOWERS
#undef QUERY_VOTERS

#define FUZZ_SLOT_MAX       (128UL)
#define FUZZ_VTR_CNT        (4UL)
#define FUZZ_ACTION_MAX     (48UL)
#define FUZZ_ROOT_SLOT      (1000UL)
#define FUZZ_EPOCH0_SLOTS   (32UL)
#define FUZZ_EPOCH1_SLOTS   (160UL)
#define FUZZ_KNOWN_MAX      (64UL)

typedef struct {
  uchar const * data;
  ulong         data_sz;
  ulong         off;
  ulong         salt;
} fuzz_reader_t;

typedef struct {
  ulong     slot;
  ulong     parent_slot;
  fd_hash_t block_id;
  fd_hash_t parent_block_id;
} fuzz_known_t;

typedef struct {
  fd_tower_tile_t ctx[1];

  fd_wksp_t * wksp;

  void * auth_vtr_mem;
  void * eqvoc_mem;
  void * ghost_mem;
  void * hfork_mem;
  void * votes_mem;
  void * tower_mem;
  void * scratch_tower_mem;
  void * publishes_mem;
  void * root_vtr_pool_mem;
  void * root_vtr_map_mem;
  void * next_vtr_pool_mem;
  void * next_vtr_map_mem;
  void * txn_tower_mem;

  fd_txn_p_t txnp[1];
  uchar      txn_meta[ FD_TXN_MAX_SZ ] __attribute__((aligned(alignof(fd_txn_t))));

  fuzz_known_t known[ FUZZ_KNOWN_MAX ];
  ulong        known_cnt;
} fuzz_env_t;

static fuzz_env_t fuzz_env[1];
static int        fuzz_env_inited;
static fd_pubkey_t fuzz_vote_acc_cache[ FUZZ_VTR_CNT ];
static fd_pubkey_t fuzz_auth_vtr_cache[ FUZZ_VTR_CNT ];
static fd_pubkey_t fuzz_id_key_cache[ FUZZ_VTR_CNT ];

static void *
fuzz_alloc( ulong align,
            ulong footprint ) {
  footprint = fd_ulong_align_up( footprint, align );
  void * mem = aligned_alloc( align, footprint );
  FD_TEST( mem );
  return mem;
}

static uchar
fuzz_u8( fuzz_reader_t * r ) {
  if( FD_LIKELY( r->off<r->data_sz ) ) return r->data[ r->off++ ];
  r->salt = 6364136223846793005UL*r->salt + 1442695040888963407UL;
  return (uchar)(r->salt >> 56);
}

static ulong
fuzz_range( fuzz_reader_t * r,
            ulong           max ) {
  if( FD_UNLIKELY( !max ) ) return 0UL;
  ulong x = 0UL;
  for( ulong i=0UL; i<8UL; i++ ) x = (x<<8) | (ulong)fuzz_u8( r );
  return x % max;
}

static void
fuzz_pubkey( fd_pubkey_t * out,
             ulong         tag,
             ulong         id ) {
  for( ulong i=0UL; i<4UL; i++ ) out->ul[ i ] = (tag<<48) ^ (id+1UL) ^ (0x9e3779b97f4a7c15UL*(i+1UL));
}

static void
fuzz_hash( fd_hash_t * out,
           ulong       slot,
           ulong       variant ) {
  for( ulong i=0UL; i<4UL; i++ ) out->ul[ i ] = (slot<<17) ^ variant ^ (0xd6e8feb86659fd93UL*(i+1UL));
  if( FD_UNLIKELY( 0==memcmp( out, &hash_null, sizeof(fd_hash_t) ) ) ) out->ul[0] = 1UL;
}

static void
fuzz_vote_acc( fd_pubkey_t * out,
               ulong         idx ) {
  if( FD_LIKELY( fuzz_env_inited && idx<FUZZ_VTR_CNT ) ) {
    *out = fuzz_vote_acc_cache[ idx ];
    return;
  }
  fuzz_pubkey( out, 0xAUL, idx );
}

static void
fuzz_auth_vtr( fd_pubkey_t * out,
               ulong         idx ) {
  if( FD_LIKELY( fuzz_env_inited && idx<FUZZ_VTR_CNT ) ) {
    *out = fuzz_auth_vtr_cache[ idx ];
    return;
  }
  fuzz_pubkey( out, 0xBUL, idx );
}

static void
fuzz_id_key( fd_pubkey_t * out,
             ulong         idx ) {
  if( FD_LIKELY( fuzz_env_inited && idx<FUZZ_VTR_CNT ) ) {
    *out = fuzz_id_key_cache[ idx ];
    return;
  }
  fuzz_pubkey( out, 0xCUL, idx );
}

static ulong
fuzz_stake( ulong idx ) {
  static ulong const stake[ FUZZ_VTR_CNT ] = { 40UL, 30UL, 20UL, 10UL };
  return stake[ idx % FUZZ_VTR_CNT ];
}

static void
fuzz_fill_voters( fd_tower_tile_t * ctx ) {
  for( ulong i=0UL; i<FUZZ_VTR_CNT; i++ ) {
    fuzz_vote_acc( &ctx->vote_accs[ i ], i );
    fuzz_id_key  ( &ctx->id_keys  [ i ], i );
  }
  ctx->vtr_cnt = FUZZ_VTR_CNT;
}

static void
fuzz_insert_epoch_voters( epoch_vtr_t *     pool,
                          epoch_vtr_map_t * map,
                          ulong *           total_stake ) {
  epoch_vtr_pool_reset( pool );
  epoch_vtr_map_reset ( map  );
  *total_stake = 0UL;
  for( ulong i=0UL; i<FUZZ_VTR_CNT; i++ ) {
    epoch_vtr_t * vtr = epoch_vtr_pool_ele_acquire( pool );
    fuzz_vote_acc( &vtr->vote_acc, i );
    fuzz_auth_vtr( &vtr->auth_vtr, i );
    vtr->stake = fuzz_stake( i );
    *total_stake += vtr->stake;
    epoch_vtr_map_ele_insert( map, vtr, pool );
  }
}

ulong
mock_query_towers( fd_tower_tile_t *            ctx,
                   fd_replay_slot_completed_t * slot_completed,
                   fd_ghost_blk_t *             ghost_blk FD_PARAM_UNUSED,
                   int *                        found_our_vote_acct,
                   ulong *                      our_vote_acct_bal ) {
  fuzz_fill_voters( ctx );

  ulong total_stake    = 0UL;
  ulong prev_voter_idx = ULONG_MAX;
  for( ulong i=0UL; i<FUZZ_VTR_CNT; i++ ) {
    ulong stake = fuzz_stake( i );
    total_stake += stake;
    prev_voter_idx = fd_tower_stakes_insert( ctx->tower, slot_completed->slot, &ctx->vote_accs[ i ], stake, prev_voter_idx );
  }

  *found_our_vote_acct = 0;
  *our_vote_acct_bal   = ULONG_MAX;
  return total_stake;
}

void
mock_query_voters( fd_tower_tile_t *            ctx,
                   fd_replay_slot_completed_t * slot_completed FD_PARAM_UNUSED,
                   ulong                        epoch ) {
  fuzz_fill_voters( ctx );
  fuzz_insert_epoch_voters( ctx->root_epoch_vtr_pool, ctx->root_epoch_vtr_map, &ctx->root_epoch_total_stake );
  fuzz_insert_epoch_voters( ctx->next_epoch_vtr_pool, ctx->next_epoch_vtr_map, &ctx->next_epoch_total_stake );
  ctx->root_epoch = epoch;

  fd_eqvoc_update_voters( ctx->eqvoc, ctx->id_keys,   ctx->vtr_cnt );
  fd_hfork_update_voters( ctx->hfork, ctx->vote_accs, ctx->vtr_cnt );
  fd_votes_update_voters( ctx->votes, ctx->vote_accs, ctx->vtr_cnt );
}

static void
fuzz_env_init_once( void ) {
  if( FD_LIKELY( fuzz_env_inited ) ) return;

  ulong slot_max = FUZZ_SLOT_MAX;
  ulong blk_max  = FUZZ_SLOT_MAX * EQVOC_MAX;
  ulong fec_max  = FUZZ_SLOT_MAX * 4UL;
  ulong pub_max  = FUZZ_SLOT_MAX * FD_TOWER_SLOT_CONFIRMED_LEVEL_CNT;
  ulong chain_cnt = epoch_vtr_map_chain_cnt_est( FUZZ_VTR_CNT );

  fuzz_env->wksp = fd_wksp_new_anonymous( FD_SHMEM_NORMAL_PAGE_SZ, 64UL, 0UL, "tower_confirm_fuzz", 0UL );
  FD_TEST( fuzz_env->wksp );

  fuzz_env->auth_vtr_mem      = fuzz_alloc( auth_vtr_align(),      auth_vtr_footprint() );
  fuzz_env->eqvoc_mem         = fuzz_alloc( fd_eqvoc_align(),      fd_eqvoc_footprint( slot_max, fec_max, PER_VTR_MAX, FUZZ_VTR_CNT ) );
  fuzz_env->ghost_mem         = fd_wksp_alloc_laddr( fuzz_env->wksp, fd_ghost_align(), fd_ghost_footprint( blk_max, FUZZ_VTR_CNT ), 1UL );
  FD_TEST( fuzz_env->ghost_mem );
  fuzz_env->hfork_mem         = fuzz_alloc( fd_hfork_align(),      fd_hfork_footprint( PER_VTR_MAX, FUZZ_VTR_CNT ) );
  fuzz_env->votes_mem         = fuzz_alloc( fd_votes_align(),      fd_votes_footprint( slot_max, FUZZ_VTR_CNT ) );
  fuzz_env->tower_mem         = fuzz_alloc( fd_tower_align(),      fd_tower_footprint( blk_max, FUZZ_VTR_CNT ) );
  fuzz_env->scratch_tower_mem = fuzz_alloc( fd_tower_vote_align(), fd_tower_vote_footprint() );
  fuzz_env->publishes_mem     = fuzz_alloc( publishes_align(),     publishes_footprint( pub_max ) );
  fuzz_env->root_vtr_pool_mem = fuzz_alloc( epoch_vtr_pool_align(), epoch_vtr_pool_footprint( FUZZ_VTR_CNT ) );
  fuzz_env->root_vtr_map_mem  = fuzz_alloc( epoch_vtr_map_align(),  epoch_vtr_map_footprint( chain_cnt ) );
  fuzz_env->next_vtr_pool_mem = fuzz_alloc( epoch_vtr_pool_align(), epoch_vtr_pool_footprint( FUZZ_VTR_CNT ) );
  fuzz_env->next_vtr_map_mem  = fuzz_alloc( epoch_vtr_map_align(),  epoch_vtr_map_footprint( chain_cnt ) );
  fuzz_env->txn_tower_mem     = fuzz_alloc( fd_tower_align(),      fd_tower_footprint( 2UL, 2UL ) );

  for( ulong i=0UL; i<FUZZ_VTR_CNT; i++ ) {
    fuzz_pubkey( &fuzz_vote_acc_cache[ i ], 0xAUL, i );
    fuzz_pubkey( &fuzz_auth_vtr_cache[ i ], 0xBUL, i );
    fuzz_pubkey( &fuzz_id_key_cache  [ i ], 0xCUL, i );
  }

  fuzz_env_inited = 1;
}

static void
fuzz_setup_leaders( fd_tower_tile_t * ctx ) {
  fd_vote_stake_weight_t stakes[1] = {{ .vote_key = {{0}}, .id_key = {{0}}, .stake = 1UL }};
  ctx->mleaders = fd_multi_epoch_leaders_join( fd_multi_epoch_leaders_new( ctx->mleaders_mem ) );
  FD_TEST( ctx->mleaders );
  ctx->mleaders->lsched[0] = fd_epoch_leaders_join( fd_epoch_leaders_new( ctx->mleaders->_lsched[0], 0UL, FUZZ_ROOT_SLOT, FUZZ_EPOCH0_SLOTS, 1UL, stakes, 0UL ) );
  ctx->mleaders->lsched[1] = fd_epoch_leaders_join( fd_epoch_leaders_new( ctx->mleaders->_lsched[1], 1UL, FUZZ_ROOT_SLOT + FUZZ_EPOCH0_SLOTS, FUZZ_EPOCH1_SLOTS, 1UL, stakes, 0UL ) );
  FD_TEST( ctx->mleaders->lsched[0] && ctx->mleaders->lsched[1] );
  ctx->mleaders->init_done[0] = 1;
  ctx->mleaders->init_done[1] = 1;
}

static void
fuzz_remember( fuzz_env_t *      env,
               ulong             slot,
               ulong             parent_slot,
               fd_hash_t const * block_id,
               fd_hash_t const * parent_block_id ) {
  if( FD_UNLIKELY( env->known_cnt==FUZZ_KNOWN_MAX ) ) return;
  env->known[ env->known_cnt++ ] = (fuzz_known_t){
    .slot            = slot,
    .parent_slot     = parent_slot,
    .block_id        = *block_id,
    .parent_block_id = *parent_block_id
  };
}

static fuzz_known_t *
fuzz_pick_known( fuzz_env_t *    env,
                 fuzz_reader_t * r ) {
  if( FD_UNLIKELY( !env->known_cnt ) ) return NULL;
  return &env->known[ fuzz_range( r, env->known_cnt ) ];
}

static void
fuzz_drain_publishes( fd_tower_tile_t * ctx ) {
  while( FD_LIKELY( !publishes_empty( ctx->publishes ) ) ) {
    publish_t * pub = publishes_pop_head_nocopy( ctx->publishes );
    switch( pub->sig ) {
    case FD_TOWER_SIG_SLOT_CONFIRMED:
      if( FD_UNLIKELY( pub->msg.slot_confirmed.fwd ) ) {
        FD_FUZZ_MUST_BE_COVERED;
      } else {
        FD_FUZZ_MUST_BE_COVERED;
      }
      break;
    case FD_TOWER_SIG_SLOT_DUPLICATE:
      FD_FUZZ_MUST_BE_COVERED;
      break;
    case FD_TOWER_SIG_SLOT_ROOTED:
      FD_FUZZ_MUST_BE_COVERED;
      break;
    case FD_TOWER_SIG_SLOT_IGNORED:
      FD_FUZZ_MUST_BE_COVERED;
      break;
    case FD_TOWER_SIG_SLOT_DONE:
      break;
    default:
      FD_TEST( 0 );
    }
  }
}

static int
fuzz_prior_vote_visible( fd_tower_tile_t * ctx ) {
  if( FD_LIKELY( fd_tower_vote_empty( ctx->tower->votes ) ) ) return 1;

  ulong            prev_vote_slot = fd_tower_vote_peek_tail_const( ctx->tower->votes )->slot;
  fd_tower_blk_t * prev_vote_fork = fd_tower_blocks_query( ctx->tower, prev_vote_slot );
  if( FD_UNLIKELY( !prev_vote_fork ) ) return 0;

  return !!fd_ghost_query( ctx->ghost, &prev_vote_fork->voted_block_id );
}

static void
fuzz_setup_case( fuzz_env_t *    env,
                 fuzz_reader_t * r ) {
  fd_tower_tile_t * ctx = env->ctx;
  memset( ctx, 0, sizeof(*ctx) );
  env->known_cnt = 0UL;

  ctx->seed = fuzz_range( r, ULONG_MAX-1UL ) + 1UL;
  ctx->checkpt_fd = -1;
  ctx->restore_fd = -1;
  fuzz_auth_vtr( ctx->identity_key, 0UL );
  fuzz_vote_acc ( ctx->vote_account, 0UL );

  ulong chain_cnt = epoch_vtr_map_chain_cnt_est( FUZZ_VTR_CNT );
  ctx->auth_vtr            = auth_vtr_join       ( auth_vtr_new       ( fuzz_env->auth_vtr_mem ) );
  ctx->eqvoc               = fd_eqvoc_join       ( fd_eqvoc_new       ( fuzz_env->eqvoc_mem, FUZZ_SLOT_MAX, FUZZ_SLOT_MAX*4UL, PER_VTR_MAX, FUZZ_VTR_CNT, ctx->seed ) );
  ctx->ghost               = fd_ghost_join       ( fd_ghost_new       ( fuzz_env->ghost_mem, FUZZ_SLOT_MAX*EQVOC_MAX, FUZZ_VTR_CNT, ctx->seed ) );
  ctx->hfork               = fd_hfork_join       ( fd_hfork_new       ( fuzz_env->hfork_mem, PER_VTR_MAX, FUZZ_VTR_CNT, ctx->seed ) );
  ctx->votes               = fd_votes_join       ( fd_votes_new       ( fuzz_env->votes_mem, FUZZ_SLOT_MAX, FUZZ_VTR_CNT, ctx->seed ) );
  ctx->tower               = fd_tower_join       ( fd_tower_new       ( fuzz_env->tower_mem, FUZZ_SLOT_MAX*EQVOC_MAX, FUZZ_VTR_CNT, ctx->seed ) );
  ctx->scratch_tower       = fd_tower_vote_join  ( fd_tower_vote_new  ( fuzz_env->scratch_tower_mem ) );
  ctx->publishes           = publishes_join      ( publishes_new      ( fuzz_env->publishes_mem, FUZZ_SLOT_MAX*FD_TOWER_SLOT_CONFIRMED_LEVEL_CNT ) );
  ctx->root_epoch_vtr_pool = epoch_vtr_pool_join ( epoch_vtr_pool_new ( fuzz_env->root_vtr_pool_mem, FUZZ_VTR_CNT ) );
  ctx->root_epoch_vtr_map  = epoch_vtr_map_join  ( epoch_vtr_map_new  ( fuzz_env->root_vtr_map_mem, chain_cnt, ctx->seed ) );
  ctx->next_epoch_vtr_pool = epoch_vtr_pool_join ( epoch_vtr_pool_new ( fuzz_env->next_vtr_pool_mem, FUZZ_VTR_CNT ) );
  ctx->next_epoch_vtr_map  = epoch_vtr_map_join  ( epoch_vtr_map_new  ( fuzz_env->next_vtr_map_mem, chain_cnt, ctx->seed ) );

  FD_TEST( ctx->auth_vtr && ctx->eqvoc && ctx->ghost && ctx->hfork && ctx->votes && ctx->tower );
  FD_TEST( ctx->scratch_tower && ctx->publishes && ctx->root_epoch_vtr_pool && ctx->root_epoch_vtr_map );
  FD_TEST( ctx->next_epoch_vtr_pool && ctx->next_epoch_vtr_map );

  fuzz_setup_leaders( ctx );
  ctx->metrics.last_vote_slot = ULONG_MAX;

  fd_hash_t root_id[1];
  fd_hash_t parent_id[1];
  fuzz_hash( root_id,   FUZZ_ROOT_SLOT,     0UL );
  fuzz_hash( parent_id, FUZZ_ROOT_SLOT-1UL, 0UL );

  fd_replay_slot_completed_t root;
  memset( &root, 0, sizeof(root) );
  root.slot            = FUZZ_ROOT_SLOT;
  root.parent_slot     = FUZZ_ROOT_SLOT - 1UL;
  root.epoch           = 0UL;
  root.bank_idx        = FUZZ_ROOT_SLOT;
  root.bank_seq        = FUZZ_ROOT_SLOT;
  root.block_id        = *root_id;
  root.parent_block_id = *parent_id;
  root.bank_hash       = *root_id;
  root.block_hash      = *root_id;

  replay_slot_completed( ctx, &root, 0UL, NULL );
  fuzz_drain_publishes( ctx );
  fuzz_remember( env, root.slot, root.parent_slot, root_id, parent_id );
}

static ulong
fuzz_replay_cnt_for_slot( fuzz_env_t const * env,
                          ulong              slot ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<env->known_cnt; i++ )
    cnt += (ulong)( env->known[ i ].slot==slot );
  return cnt;
}

static void
fuzz_replay_action( fuzz_env_t *    env,
                    fuzz_reader_t * r ) {
  fd_tower_tile_t * ctx = env->ctx;
  fuzz_known_t * parent = fuzz_pick_known( env, r );
  if( FD_UNLIKELY( !parent ) ) return;

  int use_unknown_parent = (int)(fuzz_u8( r ) & 7U)==0;
  ulong slot;
  ulong parent_slot;
  fd_hash_t parent_id[1];
  if( FD_UNLIKELY( use_unknown_parent ) ) {
    slot = FUZZ_ROOT_SLOT + 1UL + fuzz_range( r, FUZZ_SLOT_MAX-2UL );
    parent_slot = slot - 1UL;
    fuzz_hash( parent_id, slot-1UL, 0xBADUL );
  } else {
    slot = parent->slot + 1UL + fuzz_range( r, 3UL );
    parent_slot = parent->slot;
    *parent_id = parent->block_id;
  }
  if( FD_UNLIKELY( slot>=FUZZ_ROOT_SLOT + FUZZ_EPOCH0_SLOTS + FUZZ_EPOCH1_SLOTS ) ) return;
  if( FD_UNLIKELY( slot<ctx->tower->root ) ) return;

  ulong variant = 1UL + fuzz_range( r, 64UL );
  if( FD_UNLIKELY( (fuzz_u8( r ) & 7U)==0 && env->known_cnt>1UL ) ) {
    fuzz_known_t * dup = fuzz_pick_known( env, r );
    slot = dup->slot;
    parent_slot = dup->parent_slot;
    *parent_id = dup->parent_block_id;
    variant += 1000UL;
  }
  if( FD_UNLIKELY( slot<ctx->tower->root ) ) return;
  if( FD_UNLIKELY( fuzz_replay_cnt_for_slot( env, slot )>=EQVOC_MAX ) ) return;

  fd_hash_t block_id[1];
  fuzz_hash( block_id, slot, variant );
  if( FD_UNLIKELY( fd_ghost_query( ctx->ghost, block_id ) ) ) return;

  fd_replay_slot_completed_t sc;
  memset( &sc, 0, sizeof(sc) );
  sc.slot            = slot;
  sc.parent_slot     = parent_slot;
  sc.epoch           = fd_ulong_if( slot < FUZZ_ROOT_SLOT + FUZZ_EPOCH0_SLOTS, 0UL, 1UL );
  sc.bank_idx        = slot;
  sc.bank_seq        = slot;
  sc.block_id        = *block_id;
  sc.parent_block_id = *parent_id;
  sc.bank_hash       = *block_id;
  sc.block_hash      = *block_id;
  sc.is_leader       = (int)(fuzz_u8( r ) & 1U);

  if( FD_UNLIKELY( !fuzz_prior_vote_visible( ctx ) ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  replay_slot_completed( ctx, &sc, 0UL, NULL );
  if( FD_LIKELY( !use_unknown_parent && fd_ghost_query( ctx->ghost, block_id ) ) ) {
    fuzz_remember( env, slot, sc.parent_slot, block_id, parent_id );
    FD_FUZZ_MUST_BE_COVERED;
  }
  fuzz_drain_publishes( ctx );
}

static ulong
fuzz_total_stake_for_slot( fd_tower_tile_t * ctx,
                           ulong             slot ) {
  fd_epoch_leaders_t const * lsched = fd_multi_epoch_leaders_get_lsched_for_slot( ctx->mleaders, slot );
  if( FD_UNLIKELY( !lsched ) ) return ctx->root_epoch_total_stake;
  return fd_ulong_if( lsched->epoch==ctx->root_epoch, ctx->root_epoch_total_stake, ctx->next_epoch_total_stake );
}

static void
fuzz_count_votes_for_block( fd_tower_tile_t * ctx,
                            ulong             slot,
                            fd_hash_t const * block_id,
                            fuzz_reader_t *   r ) {
  ulong voter_cnt = 1UL + fuzz_range( r, FUZZ_VTR_CNT );
  for( ulong i=0UL; i<voter_cnt; i++ ) {
    int err = fd_votes_count_vote( ctx->votes, &ctx->vote_accs[ i ], fuzz_stake( i ), slot, block_id );
    if( FD_UNLIKELY( err==FD_VOTES_SUCCESS ) ) FD_FUZZ_MUST_BE_COVERED;
  }
}

static void
fuzz_confirm_action( fuzz_env_t *    env,
                     fuzz_reader_t * r ) {
  fd_tower_tile_t * ctx = env->ctx;
  fuzz_known_t * known = fuzz_pick_known( env, r );
  if( FD_UNLIKELY( !known ) ) return;

  ulong slot = known->slot;
  fd_hash_t block_id[1] = { known->block_id };
  if( FD_UNLIKELY( fuzz_u8( r ) & 1U ) ) {
    slot = ctx->tower->root + 1UL + fuzz_range( r, FUZZ_SLOT_MAX-2UL );
    fuzz_hash( block_id, slot, 0xF00DUL + fuzz_range( r, 64UL ) );
  } else if( FD_UNLIKELY( fuzz_u8( r ) & 1U ) ) {
    fuzz_hash( block_id, slot, 0xD00DUL + fuzz_range( r, 64UL ) );
  }
  if( FD_UNLIKELY( slot<=ctx->tower->root || slot>=ctx->tower->root+FUZZ_SLOT_MAX ) ) return;

  fuzz_count_votes_for_block( ctx, slot, block_id, r );
  publish_slot_confirmed( ctx, slot, block_id, fuzz_total_stake_for_slot( ctx, slot ) );
  fuzz_drain_publishes( ctx );
}

static void
fuzz_duplicate_action( fuzz_env_t *    env,
                       fuzz_reader_t * r ) {
  fd_tower_tile_t * ctx = env->ctx;
  fuzz_known_t * known = fuzz_pick_known( env, r );
  if( FD_UNLIKELY( !known ) ) return;
  if( FD_UNLIKELY( known->slot<=ctx->tower->root ) ) return;

  fd_gossip_duplicate_shred_t chunks[ FD_EQVOC_CHUNK_CNT ];
  memset( chunks, 0, sizeof(chunks) );
  for( uchar i=0U; i<FD_EQVOC_CHUNK_CNT; i++ ) {
    chunks[i].slot        = known->slot;
    chunks[i].chunk_index = i;
    chunks[i].num_chunks  = FD_EQVOC_CHUNK_CNT;
    chunks[i].chunk_len   = (ushort)fd_ulong_min( sizeof(chunks[i].chunk), 8UL + fuzz_range( r, 32UL ) );
    memset( chunks[i].chunk, (int)(known->slot + (ulong)i), chunks[i].chunk_len );
  }

  publish_slot_duplicate( ctx, chunks, known->slot );
  fuzz_drain_publishes( ctx );
}

static int
fuzz_ghost_descends_from_root( fd_tower_tile_t * ctx,
                               fd_ghost_blk_t *  blk ) {
  fd_ghost_blk_t * root = fd_ghost_root( ctx->ghost );
  for( fd_ghost_blk_t * cur = blk; cur; cur = fd_ghost_parent( ctx->ghost, cur ) ) {
    if( FD_LIKELY( cur==root ) ) return 1;
  }
  return 0;
}

static void
fuzz_root_action( fuzz_env_t *    env,
                  fuzz_reader_t * r ) {
  fd_tower_tile_t * ctx = env->ctx;
  fuzz_known_t * known = fuzz_pick_known( env, r );
  if( FD_UNLIKELY( !known || known->slot<=ctx->tower->root ) ) return;

  fd_tower_blk_t * tower_blk = fd_tower_blocks_query( ctx->tower, known->slot );
  fd_ghost_blk_t * ghost_blk = fd_ghost_query( ctx->ghost, &known->block_id );
  if( FD_UNLIKELY( !tower_blk || !ghost_blk || !ghost_blk->valid ) ) return;
  if( FD_UNLIKELY( !fuzz_ghost_descends_from_root( ctx, ghost_blk ) ) ) return;

  publish_slot_rooted( ctx, known->slot, &known->block_id );
  FD_FUZZ_MUST_BE_COVERED;

  fuzz_drain_publishes( ctx );
}

static fd_txn_t const *
fuzz_vote_txn( fuzz_env_t *      env,
               ulong             voter_idx,
               ulong             root,
               ulong             vote_cnt,
               ulong const *     slots,
               ulong const *     confs,
               fd_hash_t const * block_id,
               fd_hash_t const * bank_hash ) {
  fd_tower_t * tmp = fd_tower_join( fd_tower_new( env->txn_tower_mem, 2UL, 2UL, env->ctx->seed ) );
  FD_TEST( tmp );
  tmp->root = root;
  for( ulong i=0UL; i<vote_cnt; i++ )
    fd_tower_vote_push_tail( tmp->votes, (fd_tower_vote_t){ .slot = slots[i], .conf = confs[i] } );

  fd_hash_t recent = {{0}};
  fd_pubkey_t vote_acc[1];
  fd_pubkey_t auth[1];
  fuzz_vote_acc( vote_acc, voter_idx );
  fuzz_auth_vtr( auth, voter_idx );
  fd_tower_to_vote_txn( tmp, bank_hash, block_id, &recent, auth, auth, vote_acc, env->txnp );
  FD_TEST( env->txnp->payload_sz && env->txnp->payload_sz<=FD_TPU_MTU );
  FD_TEST( fd_txn_parse_core( env->txnp->payload, env->txnp->payload_sz, env->txn_meta, NULL, NULL ) );
  return (fd_txn_t const *)env->txn_meta;
}

static void
fuzz_vote_txn_action( fuzz_env_t *    env,
                      fuzz_reader_t * r ) {
  fd_tower_tile_t * ctx = env->ctx;
  fuzz_known_t * known = fuzz_pick_known( env, r );
  if( FD_UNLIKELY( !known ) ) return;

  ulong slots[ 4UL ];
  ulong confs[ 4UL ];
  ulong vote_cnt = 1UL + fuzz_range( r, 4UL );
  ulong first_slot = ctx->tower->root + fuzz_range( r, 3UL );
  if( FD_LIKELY( first_slot<=ctx->tower->root ) ) first_slot = ctx->tower->root + 1UL;
  for( ulong i=0UL; i<vote_cnt; i++ ) {
    slots[i] = first_slot + i;
    confs[i] = vote_cnt - i;
  }

  if( FD_UNLIKELY( (fuzz_u8( r ) & 3U)==0 ) ) {
    slots[ vote_cnt-1UL ] = known->slot;
    if( vote_cnt>1UL && slots[vote_cnt-1UL]<=slots[vote_cnt-2UL] ) slots[vote_cnt-1UL] = slots[vote_cnt-2UL] + 1UL;
  }
  if( FD_UNLIKELY( slots[vote_cnt-1UL]>=ctx->tower->root+FUZZ_SLOT_MAX ) ) return;

  fd_hash_t block_id[1];
  fd_hash_t bank_hash[1];
  if( FD_LIKELY( known->slot==slots[vote_cnt-1UL] && (fuzz_u8( r ) & 1U) ) ) *block_id = known->block_id;
  else fuzz_hash( block_id, slots[vote_cnt-1UL], 0x5151UL + fuzz_range( r, 64UL ) );
  fuzz_hash( bank_hash, slots[vote_cnt-1UL], 0x6161UL );

  if( FD_UNLIKELY( (fuzz_u8( r ) & 15U)==0 && vote_cnt>1UL ) ) confs[ vote_cnt-1UL ] = confs[ vote_cnt-2UL ];

  ulong voter_idx = fuzz_range( r, FUZZ_VTR_CNT );
  fd_txn_t const * txn = fuzz_vote_txn( env, voter_idx, ctx->tower->root, vote_cnt, slots, confs, block_id, bank_hash );
  count_vote_txn( ctx, txn, env->txnp->payload );
  fuzz_drain_publishes( ctx );
}

static void
run_duplicate_confirm_seed( fuzz_env_t *    env,
                            fuzz_reader_t * r ) {
  fd_tower_tile_t * ctx = env->ctx;
  fuzz_known_t * root = &env->known[ 0 ];

  fd_hash_t block_a[1];
  fd_hash_t block_b[1];
  fuzz_hash( block_a, FUZZ_ROOT_SLOT+1UL, 0xA11CEUL );
  fuzz_hash( block_b, FUZZ_ROOT_SLOT+1UL, 0xB0BUL   );

  fd_replay_slot_completed_t sc;
  memset( &sc, 0, sizeof(sc) );
  sc.slot            = FUZZ_ROOT_SLOT+1UL;
  sc.parent_slot     = root->slot;
  sc.epoch           = 0UL;
  sc.bank_idx        = sc.slot;
  sc.bank_seq        = sc.slot;
  sc.block_id        = *block_a;
  sc.parent_block_id = root->block_id;
  sc.bank_hash       = *block_a;
  sc.block_hash      = *block_a;
  replay_slot_completed( ctx, &sc, 0UL, NULL );
  fuzz_remember( env, sc.slot, sc.parent_slot, block_a, &root->block_id );
  fuzz_drain_publishes( ctx );

  sc.block_id  = *block_b;
  sc.bank_hash = *block_b;
  sc.block_hash = *block_b;
  replay_slot_completed( ctx, &sc, 0UL, NULL );
  fuzz_remember( env, sc.slot, sc.parent_slot, block_b, &root->block_id );
  fuzz_drain_publishes( ctx );

  fuzz_count_votes_for_block( ctx, sc.slot, block_b, r );
  publish_slot_confirmed( ctx, sc.slot, block_b, fuzz_total_stake_for_slot( ctx, sc.slot ) );
  fuzz_drain_publishes( ctx );

  FD_TEST( fuzz_prior_vote_visible( ctx ) );
  FD_FUZZ_MUST_BE_COVERED;
}

int
LLVMFuzzerInitialize( int *    argc,
                      char *** argv ) {
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );
  fd_boot( argc, argv );
  atexit( fd_halt );
  fd_log_level_core_set( 3 );
  fd_log_level_stderr_set( 4 );
  fd_log_level_logfile_set( 4 );
  fuzz_env_init_once();
  return 0;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {
  fuzz_env_init_once();

  fuzz_reader_t r = {
    .data    = data,
    .data_sz = size,
    .off     = 0UL,
    .salt    = size ^ 0x9e3779b97f4a7c15UL
  };
  fuzz_setup_case( fuzz_env, &r );

  if( FD_UNLIKELY( size && data[ 0 ]==0xf0U ) ) {
    run_duplicate_confirm_seed( fuzz_env, &r );
    return 0;
  }

  ulong action_cnt = 1UL + fuzz_range( &r, FUZZ_ACTION_MAX );
  for( ulong i=0UL; i<action_cnt; i++ ) {
    switch( fuzz_range( &r, 5UL ) ) {
    case 0UL: fuzz_replay_action   ( fuzz_env, &r ); break;
    case 1UL: fuzz_confirm_action  ( fuzz_env, &r ); break;
    case 2UL: fuzz_duplicate_action( fuzz_env, &r ); break;
    case 3UL: fuzz_root_action     ( fuzz_env, &r ); break;
    case 4UL: fuzz_vote_txn_action ( fuzz_env, &r ); break;
    default: break;
    }
  }

  fuzz_drain_publishes( fuzz_env->ctx );
  return 0;
}
