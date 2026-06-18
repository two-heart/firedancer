#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include <stdlib.h>
#include <string.h>

#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"
#include "fd_rewards_base.h"
#include "fd_stake_rewards.h"

#define FUZZ_MAX_FORKS          (8UL)
#define FUZZ_MAX_STAKE_ACCOUNTS (128UL)
#define FUZZ_EXPECTED_ACCOUNTS  (64UL)
#define FUZZ_MAX_ENTRIES        (48UL)
#define FUZZ_MAX_PARTITIONS     (16U)
#define FUZZ_MAX_ACTIONS        (96UL)

typedef struct {
  uchar const * cur;
  ulong         rem;
  ulong         salt;
} fuzz_reader_t;

typedef struct {
  fd_pubkey_t pubkey;
  ulong       lamports;
  ulong       credits_observed;
} reward_entry_t;

typedef struct {
  uchar fork_idx;
  ulong epoch;
  ulong parent_slot;
  ulong slot;
  ulong starting_block_height;
  uint  partition_cnt;

  reward_entry_t entry[ FUZZ_MAX_ENTRIES ];
  ulong          entry_cnt;
  ulong          total_rewards;
  uchar          distributed[ FUZZ_MAX_PARTITIONS ];
} fork_model_t;

typedef struct {
  fd_stake_rewards_t * stake_rewards;
  ulong                epoch;
  ulong                root_slot;
  ulong                epoch_insert_cnt;
  ulong                fork_cnt;
  fork_model_t         fork[ FUZZ_MAX_FORKS ];
} model_t;

static void * fuzz_mem;

static uchar
fuzz_u8( fuzz_reader_t * r ) {
  if( FD_LIKELY( r->rem ) ) {
    uchar x = r->cur[0];
    r->cur++;
    r->rem--;
    return x;
  }

  r->salt = 6364136223846793005UL*r->salt + 1442695040888963407UL;
  return (uchar)(r->salt >> 56);
}

static ulong
fuzz_bounded( fuzz_reader_t * r,
              ulong           bound ) {
  if( FD_UNLIKELY( bound<=1UL ) ) return 0UL;

  ulong x = 0UL;
  for( ulong shift=0UL, max=bound-1UL; max; shift+=8UL, max>>=8UL )
    x |= (ulong)fuzz_u8( r ) << shift;
  return x % bound;
}

static ulong
fuzz_u64( fuzz_reader_t * r ) {
  ulong x = 0UL;
  for( ulong i=0UL; i<8UL; i++ ) x |= (ulong)fuzz_u8( r ) << (8UL*i);
  return x;
}

static void
make_hash( fd_hash_t * out,
           ulong       epoch,
           ulong       parent_slot,
           ulong       slot,
           ulong       salt ) {
  out->ul[0] = epoch       ^ 0x9e3779b97f4a7c15UL;
  out->ul[1] = parent_slot ^ 0xbf58476d1ce4e5b9UL;
  out->ul[2] = slot        ^ 0x94d049bb133111ebUL;
  out->ul[3] = salt        ^ (epoch<<32);
}

static void
make_pubkey( fd_pubkey_t * out,
             ulong         account_id,
             ulong         salt ) {
  out->ul[0] = account_id;
  out->ul[1] = 0x7374616b655f7265UL ^ salt;
  out->ul[2] = 0x77617264735f667aUL ^ (account_id<<17);
  out->ul[3] = 0x666f726b735f667aUL ^ fd_ulong_bswap( account_id + salt );
}

static int
entry_eq( reward_entry_t const * a,
          fd_pubkey_t const *    pubkey,
          ulong                  lamports,
          ulong                  credits_observed ) {
  return !memcmp( a->pubkey.key, pubkey->key, sizeof(fd_pubkey_t) ) &&
         a->lamports==lamports &&
         a->credits_observed==credits_observed;
}

static void
validate_one_partition( model_t const *      m,
                        fork_model_t const * f,
                        uint                 partition_idx,
                        ulong *              seen_cnt,
                        ulong *              seen_rewards,
                        uchar *              seen ) {
  for( fd_stake_rewards_iter_init( m->stake_rewards, f->fork_idx, partition_idx );
       !fd_stake_rewards_iter_done( m->stake_rewards );
       fd_stake_rewards_iter_next( m->stake_rewards, f->fork_idx ) ) {
    fd_pubkey_t pubkey;
    ulong       lamports;
    ulong       credits_observed;
    fd_stake_rewards_iter_ele( m->stake_rewards, f->fork_idx, &pubkey, &lamports, &credits_observed );

    ulong match = ULONG_MAX;
    for( ulong i=0UL; i<f->entry_cnt; i++ ) {
      if( seen[i] ) continue;
      if( !entry_eq( &f->entry[i], &pubkey, lamports, credits_observed ) ) continue;
      match = i;
      break;
    }
    if( FD_UNLIKELY( match==ULONG_MAX ) ) {
      FD_LOG_ERR(( "stake rewards iterator returned an unexpected entry" ));
    }

    seen[ match ] = 1U;
    (*seen_cnt)++;
    (*seen_rewards) += lamports;
    if( FD_UNLIKELY( *seen_cnt>f->entry_cnt ) ) {
      FD_LOG_ERR(( "stake rewards iterator returned too many entries" ));
    }
  }
}

static void
validate_fork( model_t const *      m,
               fork_model_t const * f ) {
  if( FD_UNLIKELY( fd_stake_rewards_num_partitions( m->stake_rewards, f->fork_idx )!=f->partition_cnt ) ) {
    FD_LOG_ERR(( "partition count changed for fork %u", (uint)f->fork_idx ));
  }
  if( FD_UNLIKELY( fd_stake_rewards_starting_block_height( m->stake_rewards, f->fork_idx )!=f->starting_block_height ) ) {
    FD_LOG_ERR(( "starting block height changed for fork %u", (uint)f->fork_idx ));
  }
  if( FD_UNLIKELY( fd_stake_rewards_exclusive_ending_block_height( m->stake_rewards, f->fork_idx )!=
                   f->starting_block_height + (ulong)f->partition_cnt ) ) {
    FD_LOG_ERR(( "exclusive ending block height changed for fork %u", (uint)f->fork_idx ));
  }
  if( FD_UNLIKELY( fd_stake_rewards_total_rewards( m->stake_rewards, f->fork_idx )!=f->total_rewards ) ) {
    FD_LOG_ERR(( "total rewards changed for fork %u", (uint)f->fork_idx ));
  }

  uchar seen[ FUZZ_MAX_ENTRIES ] = {0};
  ulong seen_cnt     = 0UL;
  ulong seen_rewards = 0UL;
  for( uint p=0U; p<f->partition_cnt; p++ )
    validate_one_partition( m, f, p, &seen_cnt, &seen_rewards, seen );

  if( FD_UNLIKELY( seen_cnt!=f->entry_cnt ) ) {
    FD_LOG_ERR(( "stake rewards iterator dropped entries (%lu != %lu)", seen_cnt, f->entry_cnt ));
  }
  if( FD_UNLIKELY( seen_rewards!=f->total_rewards ) ) {
    FD_LOG_ERR(( "stake rewards iterator changed total rewards (%lu != %lu)", seen_rewards, f->total_rewards ));
  }
}

static void
validate_model( model_t const * m ) {
  for( ulong i=0UL; i<m->fork_cnt; i++ ) validate_fork( m, &m->fork[i] );
}

static fork_model_t *
init_fork( model_t *       m,
           fuzz_reader_t * r,
           int             force_new_epoch ) {
  if( FD_UNLIKELY( m->fork_cnt>=FUZZ_MAX_FORKS ) ) return NULL;

  int new_epoch = force_new_epoch || ( m->fork_cnt && !( fuzz_u8( r ) & 15U ) );
  if( FD_UNLIKELY( new_epoch ) ) {
    m->epoch += 1UL + fuzz_bounded( r, 4UL );
    m->fork_cnt         = 0UL;
    m->epoch_insert_cnt = 0UL;
    FD_FUZZ_MUST_BE_COVERED;
  } else if( FD_LIKELY( m->fork_cnt ) ) {
    FD_FUZZ_MUST_BE_COVERED;
  }

  ulong parent_slot;
  ulong parent_height;
  if( FD_LIKELY( m->fork_cnt ) ) {
    fork_model_t const * parent = &m->fork[ fuzz_bounded( r, m->fork_cnt ) ];
    parent_slot   = parent->slot;
    parent_height = parent->starting_block_height;
  } else {
    parent_slot   = m->root_slot;
    parent_height = m->root_slot;
  }

  ulong slot = parent_slot + 1UL + fuzz_bounded( r, 4UL );
  ulong starting_block_height = parent_height + 1UL + fuzz_bounded( r, 4UL );
  uint  partition_cnt = 1U + (uint)fuzz_bounded( r, fd_uint_min( FUZZ_MAX_PARTITIONS, (uint)MAX_PARTITIONS_PER_EPOCH ) );

  fd_hash_t parent_blockhash;
  make_hash( &parent_blockhash, m->epoch, parent_slot, slot, fuzz_u64( r ) );

  fork_model_t * f = &m->fork[ m->fork_cnt++ ];
  memset( f, 0, sizeof(fork_model_t) );
  f->epoch                 = m->epoch;
  f->parent_slot           = parent_slot;
  f->slot                  = slot;
  f->starting_block_height = starting_block_height;
  f->partition_cnt         = partition_cnt;
  f->fork_idx              = fd_stake_rewards_init( m->stake_rewards,
                                                    m->epoch,
                                                    &parent_blockhash,
                                                    starting_block_height,
                                                    partition_cnt );
  return f;
}

static void
insert_reward( model_t *       m,
               fuzz_reader_t * r ) {
  if( FD_UNLIKELY( !m->fork_cnt ) ) {
    if( FD_UNLIKELY( !init_fork( m, r, 0 ) ) ) return;
  }
  if( FD_UNLIKELY( m->epoch_insert_cnt>=FUZZ_MAX_STAKE_ACCOUNTS ) ) return;

  fork_model_t * f = &m->fork[ fuzz_bounded( r, m->fork_cnt ) ];
  if( FD_UNLIKELY( f->entry_cnt>=FUZZ_MAX_ENTRIES ) ) return;

  ulong account_id = fuzz_bounded( r, FUZZ_EXPECTED_ACCOUNTS );
  ulong salt       = (fuzz_u8( r ) & 3U) ? 0UL : f->slot;

  reward_entry_t e;
  make_pubkey( &e.pubkey, account_id, salt );
  e.lamports         = 1UL + fuzz_bounded( r, 1000000UL );
  e.credits_observed = fuzz_bounded( r, 1000000UL );

  fd_stake_rewards_insert( m->stake_rewards, f->fork_idx, &e.pubkey, e.lamports, e.credits_observed );

  f->entry[ f->entry_cnt++ ] = e;
  f->total_rewards += e.lamports;
  m->epoch_insert_cnt++;
}

static void
distribute_partition( model_t *       m,
                      fuzz_reader_t * r ) {
  if( FD_UNLIKELY( !m->fork_cnt ) ) return;

  fork_model_t * f = &m->fork[ fuzz_bounded( r, m->fork_cnt ) ];
  uint partition_idx;
  if( fuzz_u8( r ) & 1U ) {
    ulong block_height = f->starting_block_height + fuzz_bounded( r, (ulong)f->partition_cnt + 2UL );
    if( FD_UNLIKELY( block_height>=f->starting_block_height+(ulong)f->partition_cnt ) ) {
      FD_FUZZ_MUST_BE_COVERED;
      return;
    }
    partition_idx = (uint)(block_height - f->starting_block_height);
  } else {
    partition_idx = (uint)fuzz_bounded( r, f->partition_cnt );
  }

  if( FD_UNLIKELY( f->distributed[ partition_idx ] ) ) {
    FD_FUZZ_MUST_BE_COVERED;
  }
  f->distributed[ partition_idx ] = 1U;

  uchar seen[ FUZZ_MAX_ENTRIES ] = {0};
  ulong seen_cnt     = 0UL;
  ulong seen_rewards = 0UL;
  validate_one_partition( m, f, partition_idx, &seen_cnt, &seen_rewards, seen );

  if( FD_UNLIKELY( !seen_cnt ) ) {
    FD_FUZZ_MUST_BE_COVERED;
  } else {
    FD_FUZZ_MUST_BE_COVERED;
  }

  int all_done = 1;
  for( uint p=0U; p<f->partition_cnt; p++ ) all_done &= !!f->distributed[p];
  if( FD_UNLIKELY( all_done ) ) FD_FUZZ_MUST_BE_COVERED;
}

static void
clear_rewards( model_t * m ) {
  fd_stake_rewards_clear( m->stake_rewards );
  m->fork_cnt         = 0UL;
  m->epoch_insert_cnt = 0UL;
  FD_FUZZ_MUST_BE_COVERED;
}

int
LLVMFuzzerInitialize( int  *   argc,
                      char *** argv ) {
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );
  fd_boot( argc, argv );
  atexit( fd_halt );
  fd_log_level_core_set( 3 );

  ulong footprint = fd_stake_rewards_footprint( FUZZ_MAX_STAKE_ACCOUNTS,
                                                FUZZ_EXPECTED_ACCOUNTS,
                                                FUZZ_MAX_FORKS );
  fuzz_mem = aligned_alloc( fd_stake_rewards_align(), footprint );
  if( FD_UNLIKELY( !fuzz_mem ) ) FD_LOG_ERR(( "failed to allocate stake rewards fuzz memory" ));
  return 0;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         data_sz ) {
  if( FD_UNLIKELY( data_sz>512UL ) ) return -1;

  fuzz_reader_t r = {
    .cur  = data,
    .rem  = data_sz,
    .salt = 0xa5c31f27d4e6b890UL ^ data_sz
  };

  fd_stake_rewards_t * stake_rewards = fd_stake_rewards_join(
      fd_stake_rewards_new( fuzz_mem,
                            FUZZ_MAX_STAKE_ACCOUNTS,
                            FUZZ_EXPECTED_ACCOUNTS,
                            FUZZ_MAX_FORKS,
                            fuzz_u64( &r ) ) );
  if( FD_UNLIKELY( !stake_rewards ) ) FD_LOG_ERR(( "failed to initialize stake rewards" ));

  model_t m;
  memset( &m, 0, sizeof(m) );
  m.stake_rewards = stake_rewards;
  m.epoch         = 1UL + fuzz_bounded( &r, 1000000UL );
  m.root_slot     = fuzz_bounded( &r, 1000000UL );

  ulong action_cnt = 1UL + fuzz_bounded( &r, FUZZ_MAX_ACTIONS );
  for( ulong action_idx=0UL; action_idx<action_cnt; action_idx++ ) {
    uchar op = fuzz_u8( &r ) % 8U;
    switch( op ) {
    case 0:
    case 1:
      if( !init_fork( &m, &r, 0 ) ) clear_rewards( &m );
      break;
    case 2:
      (void)init_fork( &m, &r, 1 );
      break;
    case 3:
    case 4:
    case 5:
      insert_reward( &m, &r );
      break;
    case 6:
      distribute_partition( &m, &r );
      break;
    default:
      clear_rewards( &m );
      break;
    }
    validate_model( &m );
  }

  return 0;
}
