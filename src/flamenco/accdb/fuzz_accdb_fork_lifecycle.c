#define _GNU_SOURCE

#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include "fd_accdb.h"
#include "fd_accdb_cache.h"
#define FD_ACCDB_NO_FORK_ID
#include "fd_accdb_private.h"
#undef FD_ACCDB_NO_FORK_ID
#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"

#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>

#define FUZZ_MAX_LIVE_SLOTS              (32UL)
#define FUZZ_ACTIVE_FORK_CAP             (12UL)
#define FUZZ_MAX_ACCOUNTS                (256UL)
#define FUZZ_MAX_ACCOUNT_WRITES_PER_SLOT (128UL)
#define FUZZ_PARTITION_CNT               (64UL)
#define FUZZ_PARTITION_SZ                (11UL<<20UL)
#define FUZZ_CACHE_MIN_RESERVED          (1UL)
#define FUZZ_CACHE_FOOTPRINT             (16UL<<20UL)

#define FUZZ_KEY_CNT     (8UL)
#define FUZZ_DATA_MAX    (64UL)
#define FUZZ_MAX_ACTIONS (96UL)

#define SENTINEL ((fd_accdb_fork_id_t){ .val = USHORT_MAX })

typedef struct {
  uchar const * cur;
  ulong         rem;
} fuzz_cursor_t;

typedef struct {
  void *             shmem_mem;
  void *             accdb_mem;
  fd_accdb_shmem_t * shmem;
  fd_accdb_t *       accdb;
  int                fd;

  fork_pool_t fork_pool[ 1 ];

  fd_accdb_fork_id_t root;
  uchar              active[ FUZZ_MAX_LIVE_SLOTS ];
  ushort             parent[ FUZZ_MAX_LIVE_SLOTS ];
  uchar              key[ FUZZ_KEY_CNT ][ 32UL ];
  uchar              touched_key[ FUZZ_KEY_CNT ];
} fuzz_env_t;

static fuzz_env_t fuzz_env[ 1 ];
static int        fuzz_env_inited;

static void
fuzz_cleanup( void ) {
  if( FD_LIKELY( fuzz_env->fd>=0 ) ) {
    close( fuzz_env->fd );
    fuzz_env->fd = -1;
  }
  free( fuzz_env->accdb_mem );
  free( fuzz_env->shmem_mem );
  fuzz_env->accdb_mem = NULL;
  fuzz_env->shmem_mem = NULL;
  fd_halt();
}

static uchar
fuzz_u8( fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( !cur->rem ) ) return 0U;
  uchar x = cur->cur[ 0 ];
  cur->cur++;
  cur->rem--;
  return x;
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

static void
fuzz_key_init( uchar key[ 32UL ],
               ulong idx ) {
  memset( key, 0, 32UL );
  FD_STORE( ulong, key, 0xacdbf00000000000UL ^ idx );
  FD_STORE( ulong, key+8UL, 0x9e3779b97f4a7c15UL * (idx+1UL) );
}

static void
fuzz_owner_init( uchar owner[ 32UL ],
                 ulong key_idx,
                 ulong tag ) {
  memset( owner, 0, 32UL );
  owner[ 0 ] = (uchar)( 0x40U + (uchar)key_idx );
  owner[ 1 ] = (uchar)tag;
}

static void
fuzz_data_init( uchar * data,
                ulong   data_len,
                ulong   key_idx,
                ulong   tag ) {
  for( ulong i=0UL; i<data_len; i++ )
    data[ i ] = (uchar)( 0x80U ^ (uchar)key_idx ^ (uchar)tag ^ (uchar)i );
}

static void
fuzz_fork_pool_ptrs( fd_accdb_shmem_t * shmem,
                     void **            out_shpool,
                     void **            out_ele ) {
  FD_SCRATCH_ALLOC_INIT( l, shmem );
  (void)FD_SCRATCH_ALLOC_APPEND( l, FD_ACCDB_SHMEM_ALIGN,
                                 sizeof(fd_accdb_shmem_t) );
  *out_shpool = FD_SCRATCH_ALLOC_APPEND( l, fork_pool_align(),
                                         fork_pool_footprint() );
  *out_ele    = FD_SCRATCH_ALLOC_APPEND( l,
                                         alignof(fd_accdb_fork_shmem_t),
                                         shmem->max_live_slots*
                                         sizeof(fd_accdb_fork_shmem_t) );
}

static void
fuzz_model_reset( fuzz_env_t * env ) {
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) {
    env->active[ i ] = 0U;
    env->parent[ i ] = USHORT_MAX;
  }
  memset( env->touched_key, 0, sizeof(env->touched_key) );
}

static void
fuzz_model_activate( fuzz_env_t *       env,
                     fd_accdb_fork_id_t fork_id,
                     ushort             parent ) {
  FD_TEST( fork_id.val<FUZZ_MAX_LIVE_SLOTS );
  env->active[ fork_id.val ] = 1U;
  env->parent[ fork_id.val ] = parent;
}

static ulong
fuzz_active_cnt( fuzz_env_t const * env ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) cnt += !!env->active[ i ];
  return cnt;
}

static int
fuzz_has_child( fuzz_env_t const * env,
                ushort             fork_id ) {
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ )
    if( env->active[ i ] && env->parent[ i ]==fork_id ) return 1;
  return 0;
}

static int
fuzz_is_descendant_or_self( fuzz_env_t const * env,
                            ushort             fork_id,
                            ushort             ancestor_id ) {
  ushort cur = fork_id;
  for( ulong depth=0UL; depth<FUZZ_MAX_LIVE_SLOTS; depth++ ) {
    if( cur==ancestor_id ) return 1;
    if( cur>=FUZZ_MAX_LIVE_SLOTS || !env->active[ cur ] ) return 0;
    cur = env->parent[ cur ];
    if( cur==USHORT_MAX ) return 0;
  }
  return 0;
}

static void
fuzz_model_purge_subtree( fuzz_env_t * env,
                          ushort       fork_id ) {
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) {
    if( env->active[ i ] && env->parent[ i ]==fork_id )
      fuzz_model_purge_subtree( env, (ushort)i );
  }

  env->active[ fork_id ] = 0U;
  env->parent[ fork_id ] = USHORT_MAX;
}

static void
fuzz_model_advance_root( fuzz_env_t *       env,
                         fd_accdb_fork_id_t new_root ) {
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) {
    if( env->active[ i ] &&
        !fuzz_is_descendant_or_self( env, (ushort)i, new_root.val ) ) {
      env->active[ i ] = 0U;
      env->parent[ i ] = USHORT_MAX;
    }
  }

  env->root                 = new_root;
  env->active[ new_root.val ] = 1U;
  env->parent[ new_root.val ] = USHORT_MAX;
}

static fd_accdb_fork_id_t
fuzz_pick_active( fuzz_env_t const * env,
                  fuzz_cursor_t *    cur ) {
  ulong cnt = fuzz_active_cnt( env );
  FD_TEST( cnt );
  ulong pick = fuzz_bounded( cur, cnt );

  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !env->active[ i ] ) ) continue;
    if( FD_UNLIKELY( !pick-- ) ) return (fd_accdb_fork_id_t){ .val = (ushort)i };
  }
  FD_LOG_ERR(( "unreachable" ));
}

static fd_accdb_fork_id_t
fuzz_pick_leaf( fuzz_env_t const * env,
                fuzz_cursor_t *    cur ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ )
    if( env->active[ i ] && !fuzz_has_child( env, (ushort)i ) ) cnt++;

  FD_TEST( cnt );
  ulong pick = fuzz_bounded( cur, cnt );
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !env->active[ i ] || fuzz_has_child( env, (ushort)i ) ) ) continue;
    if( FD_UNLIKELY( !pick-- ) ) return (fd_accdb_fork_id_t){ .val = (ushort)i };
  }
  FD_LOG_ERR(( "unreachable" ));
}

static fd_accdb_fork_id_t
fuzz_pick_nonroot( fuzz_env_t const * env,
                   fuzz_cursor_t *    cur ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ )
    if( env->active[ i ] && i!=(ulong)env->root.val ) cnt++;
  if( FD_UNLIKELY( !cnt ) ) return SENTINEL;

  ulong pick = fuzz_bounded( cur, cnt );
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !env->active[ i ] || i==(ulong)env->root.val ) ) continue;
    if( FD_UNLIKELY( !pick-- ) ) return (fd_accdb_fork_id_t){ .val = (ushort)i };
  }
  FD_LOG_ERR(( "unreachable" ));
}

static fd_accdb_fork_id_t
fuzz_pick_nonroot_leaf( fuzz_env_t const * env,
                        fuzz_cursor_t *    cur ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ )
    if( env->active[ i ] && i!=(ulong)env->root.val &&
        !fuzz_has_child( env, (ushort)i ) ) cnt++;
  if( FD_UNLIKELY( !cnt ) ) return SENTINEL;

  ulong pick = fuzz_bounded( cur, cnt );
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !env->active[ i ] || i==(ulong)env->root.val ||
                     fuzz_has_child( env, (ushort)i ) ) ) continue;
    if( FD_UNLIKELY( !pick-- ) ) return (fd_accdb_fork_id_t){ .val = (ushort)i };
  }
  FD_LOG_ERR(( "unreachable" ));
}

static fd_accdb_fork_id_t
fuzz_pick_root_child( fuzz_env_t const * env,
                      fuzz_cursor_t *    cur ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ )
    if( env->active[ i ] && env->parent[ i ]==env->root.val ) cnt++;
  if( FD_UNLIKELY( !cnt ) ) return SENTINEL;

  ulong pick = fuzz_bounded( cur, cnt );
  for( ulong i=0UL; i<FUZZ_MAX_LIVE_SLOTS; i++ ) {
    if( FD_UNLIKELY( !env->active[ i ] || env->parent[ i ]!=env->root.val ) ) continue;
    if( FD_UNLIKELY( !pick-- ) ) return (fd_accdb_fork_id_t){ .val = (ushort)i };
  }
  FD_LOG_ERR(( "unreachable" ));
}

static void
fuzz_assert_fork_links( fuzz_env_t * env ) {
  FD_TEST( env->shmem->root_fork_id.val==env->root.val );
  FD_TEST( env->root.val<FUZZ_MAX_LIVE_SLOTS );
  FD_TEST( env->active[ env->root.val ] );

  for( ulong id=0UL; id<FUZZ_MAX_LIVE_SLOTS; id++ ) {
    if( !env->active[ id ] ) continue;

    fd_accdb_fork_shmem_t * fork = fork_pool_ele( env->fork_pool, id );
    FD_TEST( fork );
    FD_TEST( fork->parent_id.val==env->parent[ id ] );

    uchar seen_child[ FUZZ_MAX_LIVE_SLOTS ];
    memset( seen_child, 0, sizeof(seen_child) );

    ushort child_id = fork->child_id.val;
    for( ulong depth=0UL; child_id!=USHORT_MAX; depth++ ) {
      FD_TEST( depth<FUZZ_MAX_LIVE_SLOTS );
      FD_TEST( child_id<FUZZ_MAX_LIVE_SLOTS );
      FD_TEST( env->active[ child_id ] );
      FD_TEST( env->parent[ child_id ]==id );
      FD_TEST( !seen_child[ child_id ] );
      seen_child[ child_id ] = 1U;

      fd_accdb_fork_shmem_t * child = fork_pool_ele( env->fork_pool,
                                                     child_id );
      FD_TEST( child );
      child_id = child->sibling_id.val;
    }

    for( ulong child=0UL; child<FUZZ_MAX_LIVE_SLOTS; child++ )
      if( env->active[ child ] && env->parent[ child ]==id )
        FD_TEST( seen_child[ child ] );
  }
}

static void
fuzz_drain_cmd( fuzz_env_t * env ) {
  int charge_busy = 0;
  fd_accdb_background( env->accdb, &charge_busy );
  FD_TEST( charge_busy );
}

static void
fuzz_env_init_once( fuzz_env_t * env ) {
  if( FD_LIKELY( fuzz_env_inited ) ) return;

  memset( env, 0, sizeof(fuzz_env_t) );
  env->fd = -1;

  env->fd = memfd_create( "accdb_fork_lifecycle_fuzz", 0 );
  if( FD_UNLIKELY( env->fd<0 ) ) FD_LOG_ERR(( "memfd_create failed" ));

  ulong shmem_fp = fd_accdb_shmem_footprint(
      FUZZ_MAX_ACCOUNTS, FUZZ_MAX_LIVE_SLOTS,
      FUZZ_MAX_ACCOUNT_WRITES_PER_SLOT, FUZZ_PARTITION_CNT,
      FUZZ_CACHE_FOOTPRINT, FUZZ_CACHE_MIN_RESERVED, 1UL );
  FD_TEST( shmem_fp );
  env->shmem_mem = aligned_alloc( fd_accdb_shmem_align(),
                                  FD_ULONG_ALIGN_UP( shmem_fp,
                                                     fd_accdb_shmem_align() ) );
  FD_TEST( env->shmem_mem );

  ulong accdb_fp = fd_accdb_footprint( FUZZ_MAX_LIVE_SLOTS );
  FD_TEST( accdb_fp );
  env->accdb_mem = aligned_alloc( fd_accdb_align(),
                                  FD_ULONG_ALIGN_UP( accdb_fp,
                                                     fd_accdb_align() ) );
  FD_TEST( env->accdb_mem );

  for( ulong i=0UL; i<FUZZ_KEY_CNT; i++ ) fuzz_key_init( env->key[ i ], i );

  fuzz_env_inited = 1;
}

static void
fuzz_setup( fuzz_env_t * env ) {
  fuzz_env_init_once( env );

  env->shmem = fd_accdb_shmem_join( fd_accdb_shmem_new(
      env->shmem_mem, FUZZ_MAX_ACCOUNTS, FUZZ_MAX_LIVE_SLOTS,
      FUZZ_MAX_ACCOUNT_WRITES_PER_SLOT, FUZZ_PARTITION_CNT,
      FUZZ_PARTITION_SZ, FUZZ_CACHE_FOOTPRINT, FUZZ_CACHE_MIN_RESERVED,
      0, 0xf17eda2ce7accdb0UL, 1UL ) );
  FD_TEST( env->shmem );

  env->accdb = fd_accdb_join( fd_accdb_new( env->accdb_mem, env->shmem,
                                            env->fd, 0UL, NULL ) );
  FD_TEST( env->accdb );

  void * fork_pool_shmem;
  void * fork_pool_ele_mem;
  fuzz_fork_pool_ptrs( env->shmem, &fork_pool_shmem, &fork_pool_ele_mem );
  FD_TEST( fork_pool_join( env->fork_pool, fork_pool_shmem,
                           fork_pool_ele_mem, FUZZ_MAX_LIVE_SLOTS ) );

  fuzz_model_reset( env );
  env->root = fd_accdb_attach_child( env->accdb, SENTINEL );
  fuzz_model_activate( env, env->root, USHORT_MAX );
  fuzz_assert_fork_links( env );
}

static void
fuzz_teardown( fuzz_env_t * env ) {
  (void)env;
}

static fd_accdb_fork_id_t
fuzz_attach_child( fuzz_env_t *    env,
                   fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( fuzz_active_cnt( env )>=FUZZ_ACTIVE_FORK_CAP ) )
    return SENTINEL;

  fd_accdb_fork_id_t parent = fuzz_pick_active( env, cur );
  fd_accdb_fork_id_t child  = fd_accdb_attach_child( env->accdb, parent );
  fuzz_model_activate( env, child, parent.val );
  fuzz_assert_fork_links( env );
  FD_FUZZ_MUST_BE_COVERED;
  return child;
}

static void
fuzz_write_acquire( fuzz_env_t *       env,
                    fuzz_cursor_t *    cur,
                    fd_accdb_fork_id_t fork_id,
                    ulong              key_idx,
                    int                commit ) {
  uchar const * pks[ 1 ] = { env->key[ key_idx ] };
  int writable[ 1 ] = { 1 };
  fd_acc_t acc[ 1 ];
  memset( acc, 0, sizeof(acc) );

  fd_accdb_acquire( env->accdb, fork_id, 1UL, pks, writable, acc );

  int tombstone = !( fuzz_u8( cur ) & 7U );
  ulong tag     = fuzz_u8( cur );
  ulong data_len = tombstone ? 0UL : fuzz_bounded( cur, FUZZ_DATA_MAX+1UL );

  acc[ 0 ].lamports   = tombstone ? 0UL : 1UL + fuzz_bounded( cur, 1000000UL );
  acc[ 0 ].data_len   = data_len;
  acc[ 0 ].executable = !!( fuzz_u8( cur ) & 1U );
  fuzz_owner_init( acc[ 0 ].owner, key_idx, tag );
  if( data_len ) fuzz_data_init( acc[ 0 ].data, data_len, key_idx, tag );
  acc[ 0 ].commit = commit;

  fd_accdb_release( env->accdb, 1UL, acc );
  env->touched_key[ key_idx ] = 1U;

  if( commit ) FD_FUZZ_MUST_BE_COVERED;
  else         FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_read_acquire( fuzz_env_t *       env,
                   fd_accdb_fork_id_t fork_id,
                   ulong              key_idx ) {
  uchar const * pks[ 1 ] = { env->key[ key_idx ] };
  int writable[ 1 ] = { 0 };
  fd_acc_t acc[ 1 ];
  memset( acc, 0, sizeof(acc) );

  fd_accdb_acquire( env->accdb, fork_id, 1UL, pks, writable, acc );
  ulong lamports = acc[ 0 ].lamports;
  fd_accdb_release( env->accdb, 1UL, acc );

  int exists = fd_accdb_exists( env->accdb, fork_id, env->key[ key_idx ] );
  FD_TEST( exists==(lamports!=0UL) );
  FD_TEST( fd_accdb_lamports( env->accdb, fork_id,
                              env->key[ key_idx ] )==lamports );

  if( lamports ) FD_FUZZ_MUST_BE_COVERED;
  else           FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_read_one( fuzz_env_t *       env,
               fd_accdb_fork_id_t fork_id,
               ulong              key_idx ) {
  fd_acc_t acc = fd_accdb_read_one( env->accdb, fork_id,
                                    env->key[ key_idx ] );
  ulong lamports = acc.lamports;
  fd_accdb_unread_one( env->accdb, &acc );

  FD_TEST( fd_accdb_exists( env->accdb, fork_id,
                            env->key[ key_idx ] )==(lamports!=0UL) );
  if( lamports ) FD_FUZZ_MUST_BE_COVERED;
  else           FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_write_one( fuzz_env_t *       env,
                fuzz_cursor_t *    cur,
                fd_accdb_fork_id_t fork_id,
                ulong              key_idx ) {
  fd_acc_t acc = fd_accdb_write_one( env->accdb, fork_id,
                                     env->key[ key_idx ] );

  int commit = !!( fuzz_u8( cur ) & 1U );
  int tombstone = !( fuzz_u8( cur ) & 7U );
  ulong tag = fuzz_u8( cur );
  ulong data_len = tombstone ? 0UL : fuzz_bounded( cur, FUZZ_DATA_MAX+1UL );

  acc.lamports   = tombstone ? 0UL : 1UL + fuzz_bounded( cur, 1000000UL );
  acc.data_len   = data_len;
  acc.executable = !!( fuzz_u8( cur ) & 1U );
  fuzz_owner_init( acc.owner, key_idx, tag );
  if( data_len ) fuzz_data_init( acc.data, data_len, key_idx, tag );
  acc.commit = commit;

  fd_accdb_unwrite_one( env->accdb, &acc );
  env->touched_key[ key_idx ] = 1U;

  if( commit ) FD_FUZZ_MUST_BE_COVERED;
  else         FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_snapshot_full_write( fuzz_env_t *    env,
                          fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( fuzz_active_cnt( env )!=1UL ) ) return;

  ulong key_idx = fuzz_bounded( cur, FUZZ_KEY_CNT );
  if( FD_UNLIKELY( env->touched_key[ key_idx ] ) ) {
    for( ulong i=0UL; i<FUZZ_KEY_CNT; i++ ) {
      ulong alt = (key_idx+i+1UL) % FUZZ_KEY_CNT;
      if( FD_LIKELY( !env->touched_key[ alt ] ) ) {
        key_idx = alt;
        break;
      }
    }
    if( FD_UNLIKELY( env->touched_key[ key_idx ] ) ) return;
  }
  env->touched_key[ key_idx ] = 1U;

  ulong slot = fuzz_bounded( cur, 128UL );
  ulong lamports = 1UL + fuzz_bounded( cur, 1000000UL );
  ulong data_len = fuzz_bounded( cur, FUZZ_DATA_MAX+1UL );
  int executable = !!( fuzz_u8( cur ) & 1U );
  ulong replaced = 0UL;

  fd_accdb_snapshot_load_begin( env->accdb );
  int rc = fd_accdb_snapshot_write_one( env->accdb, SENTINEL,
                                        env->key[ key_idx ], slot, lamports,
                                        data_len, executable, &replaced );
  fd_accdb_snapshot_load_end( env->accdb );

  FD_TEST( rc==1 || rc==2 || rc==-1 );
  FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_snapshot_incremental_revert( fuzz_env_t *    env,
                                  fuzz_cursor_t * cur ) {
  fd_accdb_fork_id_t fork_id = fuzz_pick_nonroot_leaf( env, cur );
  if( FD_UNLIKELY( fork_id.val==USHORT_MAX ) ) {
    fd_accdb_fork_id_t child = fuzz_attach_child( env, cur );
    if( FD_UNLIKELY( child.val==USHORT_MAX ) ) return;
    fork_id = child;
  }

  fd_accdb_snapshot_recovery_t recovery;
  fd_accdb_snapshot_save_whead( env->accdb, &recovery );

  fd_accdb_snapshot_load_begin( env->accdb );
  ulong write_cnt = 1UL + fuzz_bounded( cur, 2UL );
  for( ulong i=0UL; i<write_cnt; i++ ) {
    ulong key_idx = fuzz_bounded( cur, FUZZ_KEY_CNT );
    if( FD_UNLIKELY( env->touched_key[ key_idx ] ) ) continue;
    ulong slot = 128UL + fuzz_bounded( cur, 128UL );
    ulong lamports = 1UL + fuzz_bounded( cur, 1000000UL );
    ulong data_len = fuzz_bounded( cur, FUZZ_DATA_MAX+1UL );
    int executable = !!( fuzz_u8( cur ) & 1U );
    ulong replaced = 0UL;
    int rc = fd_accdb_snapshot_write_one( env->accdb, fork_id,
                                          env->key[ key_idx ], slot,
                                          lamports, data_len, executable,
                                          &replaced );
    FD_TEST( rc==1 || rc==2 || rc==-1 );
    env->touched_key[ key_idx ] = 1U;
  }
  fd_accdb_snapshot_load_end( env->accdb );

  fd_accdb_purge( env->accdb, fork_id );
  fuzz_drain_cmd( env );
  fuzz_model_purge_subtree( env, fork_id.val );

  fd_accdb_snapshot_revert_whead( env->accdb, &recovery );
  fuzz_assert_fork_links( env );
  FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_duplicate_snapshot_batch_seed( fuzz_env_t * env ) {
  uchar const * pks[ 3UL ] = { env->key[ 0 ], env->key[ 1 ], env->key[ 0 ] };
  ulong slots      [ 3UL ] = { 77UL, 77UL, 77UL };
  ulong lamports   [ 3UL ] = { 11UL, 22UL, 33UL };
  ulong data_lens  [ 3UL ] = { 0UL, 0UL, 0UL };
  int   executable [ 3UL ] = { 0, 0, 0 };

  ulong ignored           = ULONG_MAX;
  ulong replaced          = ULONG_MAX;
  ulong loaded            = ULONG_MAX;
  ulong replaced_lamports = ULONG_MAX;
  ulong ignored_lamports  = ULONG_MAX;

  fd_accdb_snapshot_load_begin( env->accdb );
  fd_log_level_core_set( 4 );
  int rc = fd_accdb_snapshot_write_batch( env->accdb, SENTINEL, 3UL,
                                          pks, slots, lamports, data_lens,
                                          executable, &ignored, &replaced,
                                          &loaded, &replaced_lamports,
                                          &ignored_lamports );
  fd_log_level_core_set( 3 );
  fd_accdb_snapshot_load_end( env->accdb );

  FD_TEST( rc==-1 );
  FD_TEST( !fd_accdb_exists( env->accdb, env->root, env->key[ 0 ] ) );
  FD_TEST( !fd_accdb_exists( env->accdb, env->root, env->key[ 1 ] ) );
  FD_FUZZ_MUST_BE_COVERED;
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
  fuzz_env_init_once( fuzz_env );
  atexit( fuzz_cleanup );
  return 0;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {
  if( FD_UNLIKELY( !size ) ) return 0;

  fuzz_cursor_t cur = { .cur = data, .rem = size };
  fuzz_setup( fuzz_env );

  if( FD_UNLIKELY( data[ 0 ]==0xf0U ) ) {
    fuzz_duplicate_snapshot_batch_seed( fuzz_env );
    fuzz_teardown( fuzz_env );
    return 0;
  }

  ulong action_cnt = 1UL + fuzz_bounded( &cur, FUZZ_MAX_ACTIONS );
  for( ulong action_idx=0UL; (action_idx<action_cnt) & !!cur.rem; action_idx++ ) {
    ulong action = fuzz_bounded( &cur, 11UL );
    ulong key_idx = fuzz_bounded( &cur, FUZZ_KEY_CNT );

    switch( action ) {
      case 0UL: {
        (void)fuzz_attach_child( fuzz_env, &cur );
        break;
      }

      case 1UL: {
        fd_accdb_fork_id_t fork_id = fuzz_pick_leaf( fuzz_env, &cur );
        fuzz_write_acquire( fuzz_env, &cur, fork_id, key_idx, 1 );
        break;
      }

      case 2UL: {
        fd_accdb_fork_id_t fork_id = fuzz_pick_leaf( fuzz_env, &cur );
        fuzz_write_acquire( fuzz_env, &cur, fork_id, key_idx, 0 );
        break;
      }

      case 3UL: {
        fd_accdb_fork_id_t fork_id = fuzz_pick_active( fuzz_env, &cur );
        fuzz_read_acquire( fuzz_env, fork_id, key_idx );
        break;
      }

      case 4UL: {
        fd_accdb_fork_id_t fork_id = fuzz_pick_active( fuzz_env, &cur );
        fuzz_read_one( fuzz_env, fork_id, key_idx );
        break;
      }

      case 5UL: {
        fd_accdb_fork_id_t fork_id = fuzz_pick_leaf( fuzz_env, &cur );
        fuzz_write_one( fuzz_env, &cur, fork_id, key_idx );
        break;
      }

      case 6UL: {
        fd_accdb_fork_id_t child = fuzz_pick_root_child( fuzz_env, &cur );
        if( FD_UNLIKELY( child.val==USHORT_MAX ) )
          child = fuzz_attach_child( fuzz_env, &cur );
        if( FD_UNLIKELY( child.val==USHORT_MAX ) ) break;

        ulong before = fuzz_active_cnt( fuzz_env );
        fd_accdb_advance_root( fuzz_env->accdb, child );
        fuzz_drain_cmd( fuzz_env );
        fuzz_model_advance_root( fuzz_env, child );
        fuzz_assert_fork_links( fuzz_env );
        if( fuzz_active_cnt( fuzz_env )<before ) FD_FUZZ_MUST_BE_COVERED;
        break;
      }

      case 7UL: {
        fd_accdb_fork_id_t fork_id = fuzz_pick_nonroot( fuzz_env, &cur );
        if( FD_UNLIKELY( fork_id.val==USHORT_MAX ) )
          fork_id = fuzz_attach_child( fuzz_env, &cur );
        if( FD_UNLIKELY( fork_id.val==USHORT_MAX ) ) break;

        fd_accdb_purge( fuzz_env->accdb, fork_id );
        fuzz_drain_cmd( fuzz_env );
        fuzz_model_purge_subtree( fuzz_env, fork_id.val );
        fuzz_assert_fork_links( fuzz_env );
        FD_FUZZ_MUST_BE_COVERED;
        break;
      }

      case 8UL:
        fuzz_snapshot_full_write( fuzz_env, &cur );
        break;

      case 9UL:
        fuzz_snapshot_incremental_revert( fuzz_env, &cur );
        break;

      default: {
        fuzz_assert_fork_links( fuzz_env );
        FD_FUZZ_MUST_BE_COVERED;
        break;
      }
    }

    fuzz_assert_fork_links( fuzz_env );
  }

  fuzz_teardown( fuzz_env );
  return 0;
}
