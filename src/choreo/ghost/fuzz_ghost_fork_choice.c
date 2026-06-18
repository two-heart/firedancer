#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include <stdlib.h>
#include <string.h>

#include "fd_ghost.h"
#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"

/* Keep the synthetic worlds small enough that every post-action
   invariant can walk the whole tree and all voters cheaply. */
#define FUZZ_BLK_MAX    (16UL)
#define FUZZ_VOTER_MAX  ( 8UL)
#define FUZZ_ACTION_MAX (96UL)
#define FUZZ_STAKE_MAX  (64UL)
#define FUZZ_WKSP_PAGES (64UL)

typedef struct {
  uchar const * data;
  ulong         data_sz;
  ulong         off;
  ulong         salt;
} fuzz_cursor_t;

typedef struct {
  fd_hash_t id;
  ulong     parent_idx;
  ulong     slot;
  int       live;
} fuzz_blk_t;

typedef struct {
  ulong blk_idx;
  ulong slot;
  ulong stake;
  int   active;
} fuzz_voter_t;

typedef struct {
  void *         mem;
  fd_ghost_t *   ghost;
  fuzz_blk_t     blk[ FUZZ_BLK_MAX ];
  fuzz_voter_t   voter[ FUZZ_VOTER_MAX ];
  ulong          blk_cnt;
  ulong          root_idx;
  ulong          last_root_slot;
} fuzz_case_t;

static fd_wksp_t * fuzz_wksp;
static void *      fuzz_ghost_mem;

static void
fuzz_cleanup( void ) {
  if( FD_LIKELY( fuzz_wksp ) ) {
    fd_wksp_delete_anonymous( fuzz_wksp );
    fuzz_wksp = NULL;
  }
  fd_halt();
}

static uchar
fuzz_u8( fuzz_cursor_t * cur ) {
  if( FD_LIKELY( cur->off<cur->data_sz ) ) return cur->data[ cur->off++ ];
  cur->salt = 6364136223846793005UL*cur->salt + 1442695040888963407UL;
  return (uchar)(cur->salt >> 56);
}

/* bound is exclusive */
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
fuzz_hash( fd_hash_t * h,
           ulong       idx,
           ulong       salt ) {
  h->ul[ 0 ] = 0x9ae16a3b2f90404fUL ^ idx;
  h->ul[ 1 ] = 0xc949d7c7509e6557UL ^ (idx << 17) ^ salt;
  h->ul[ 2 ] = 0xff51afd7ed558ccdUL ^ (idx * 0x100000001b3UL);
  h->ul[ 3 ] = 0xc4ceb9fe1a85ec53UL ^ (salt << 1);
}

static fd_pubkey_t
fuzz_pubkey( ulong idx ) {
  fd_pubkey_t key;
  for( ulong i=0UL; i<4UL; i++ )
    key.ul[ i ] = 0x4f1bbcdc8d77cdb5UL ^ idx ^ (0x9e3779b97f4a7c15UL*i);
  return key;
}

static int
fuzz_is_descendant( fuzz_case_t const * c,
                    ulong               child_idx,
                    ulong               ancestor_idx ) {
  for( ulong idx=child_idx; idx!=ULONG_MAX; idx=c->blk[ idx ].parent_idx ) {
    if( FD_UNLIKELY( idx==ancestor_idx ) ) return 1;
    if( FD_UNLIKELY( idx>=c->blk_cnt ) ) break;
  }
  return 0;
}

static ulong
fuzz_live_cnt( fuzz_case_t const * c ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<c->blk_cnt; i++ ) cnt += !!c->blk[ i ].live;
  return cnt;
}

static ulong
fuzz_pick_live( fuzz_case_t const * c,
                fuzz_cursor_t *     cur ) {
  ulong n = fuzz_bounded( cur, fuzz_live_cnt( c ) );
  for( ulong i=0UL; i<c->blk_cnt; i++ ) {
    if( FD_UNLIKELY( !c->blk[ i ].live ) ) continue;
    if( FD_UNLIKELY( !n-- ) ) return i;
  }
  return c->root_idx;
}

static int
fuzz_pick_live_nonroot( fuzz_case_t const * c,
                        fuzz_cursor_t *     cur,
                        ulong *             out_idx ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<c->blk_cnt; i++ ) cnt += !!( c->blk[ i ].live && i!=c->root_idx );
  if( FD_UNLIKELY( !cnt ) ) return 0;

  ulong n = fuzz_bounded( cur, cnt );
  for( ulong i=0UL; i<c->blk_cnt; i++ ) {
    if( FD_UNLIKELY( !( c->blk[ i ].live && i!=c->root_idx ) ) ) continue;
    if( FD_UNLIKELY( !n-- ) ) {
      *out_idx = i;
      return 1;
    }
  }

  return 0;
}

static int
fuzz_pick_duplicate_parent( fuzz_case_t const * c,
                            fuzz_cursor_t *     cur,
                            ulong *             out_parent_idx,
                            ulong *             out_child_idx ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<c->blk_cnt; i++ ) {
    if( FD_UNLIKELY( !c->blk[ i ].live ) ) continue;
    for( ulong j=0UL; j<c->blk_cnt; j++ )
      cnt += !!( c->blk[ j ].live && c->blk[ j ].parent_idx==i );
  }
  if( FD_UNLIKELY( !cnt ) ) return 0;

  ulong n = fuzz_bounded( cur, cnt );
  for( ulong i=0UL; i<c->blk_cnt; i++ ) {
    if( FD_UNLIKELY( !c->blk[ i ].live ) ) continue;
    for( ulong j=0UL; j<c->blk_cnt; j++ ) {
      if( FD_UNLIKELY( !( c->blk[ j ].live && c->blk[ j ].parent_idx==i ) ) ) continue;
      if( FD_UNLIKELY( !n-- ) ) {
        *out_parent_idx = i;
        *out_child_idx  = j;
        return 1;
      }
    }
  }

  return 0;
}

static int
fuzz_pick_publish_root( fuzz_case_t * c,
                        fuzz_cursor_t * cur,
                        ulong *         out_idx ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<c->blk_cnt; i++ ) {
    if( FD_UNLIKELY( !( c->blk[ i ].live && i!=c->root_idx ) ) ) continue;
    fd_ghost_blk_t * blk = fd_ghost_query( c->ghost, &c->blk[ i ].id );
    cnt += !!( blk && blk->valid && !fd_ghost_invalid_ancestor( c->ghost, blk ) );
  }
  if( FD_UNLIKELY( !cnt ) ) return 0;

  ulong n = fuzz_bounded( cur, cnt );
  for( ulong i=0UL; i<c->blk_cnt; i++ ) {
    if( FD_UNLIKELY( !( c->blk[ i ].live && i!=c->root_idx ) ) ) continue;
    fd_ghost_blk_t * blk = fd_ghost_query( c->ghost, &c->blk[ i ].id );
    if( FD_UNLIKELY( !( blk && blk->valid && !fd_ghost_invalid_ancestor( c->ghost, blk ) ) ) ) continue;
    if( FD_UNLIKELY( !n-- ) ) {
      *out_idx = i;
      return 1;
    }
  }

  return 0;
}

static fd_ghost_blk_t *
fuzz_insert_block( fuzz_case_t *  c,
                   ulong          parent_idx,
                   ulong          slot,
                   fuzz_cursor_t * cur ) {
  FD_TEST( c->blk_cnt<FUZZ_BLK_MAX );
  ulong idx = c->blk_cnt++;

  fuzz_hash( &c->blk[ idx ].id, idx, cur->salt ^ fuzz_u8( cur ) );
  c->blk[ idx ].parent_idx = parent_idx;
  c->blk[ idx ].slot       = slot;
  c->blk[ idx ].live       = 1;

  fd_ghost_blk_t * blk = fd_ghost_insert( c->ghost,
                                          idx,
                                          slot,
                                          &c->blk[ idx ].id,
                                          &c->blk[ parent_idx ].id );
  FD_TEST( blk );
  return blk;
}

static void
fuzz_reconcile_publish( fuzz_case_t * c,
                        ulong         new_root_idx ) {
  for( ulong i=0UL; i<c->blk_cnt; i++ )
    c->blk[ i ].live = c->blk[ i ].live && fuzz_is_descendant( c, i, new_root_idx );

  c->blk[ new_root_idx ].parent_idx = ULONG_MAX;
  c->root_idx                       = new_root_idx;

  for( ulong i=0UL; i<FUZZ_VOTER_MAX; i++ )
    if( FD_UNLIKELY( c->voter[ i ].active && !c->blk[ c->voter[ i ].blk_idx ].live ) )
      c->voter[ i ].active = 0;
}

static void
fuzz_expect_stakes( fuzz_case_t * c ) {
  ulong expected[ FUZZ_BLK_MAX ] = {0};

  for( ulong i=0UL; i<FUZZ_VOTER_MAX; i++ ) {
    if( FD_UNLIKELY( !c->voter[ i ].active ) ) continue;

    FD_TEST( c->voter[ i ].blk_idx<c->blk_cnt );
    FD_TEST( c->blk[ c->voter[ i ].blk_idx ].live );

    for( ulong idx=c->voter[ i ].blk_idx; idx!=ULONG_MAX; idx=c->blk[ idx ].parent_idx ) {
      ulong sum;
      FD_TEST( !__builtin_uaddl_overflow( expected[ idx ], c->voter[ i ].stake, &sum ) );
      expected[ idx ] = sum;
      if( FD_UNLIKELY( idx==c->root_idx ) ) break;
      FD_TEST( idx<c->blk_cnt );
    }
  }

  for( ulong i=0UL; i<c->blk_cnt; i++ ) {
    fd_ghost_blk_t * blk = fd_ghost_query( c->ghost, &c->blk[ i ].id );
    if( FD_LIKELY( c->blk[ i ].live ) ) {
      FD_TEST( blk );
      FD_TEST( blk->stake==expected[ i ] );
      FD_TEST( blk->slot==c->blk[ i ].slot );
    } else {
      FD_TEST( !blk );
    }
  }
}

static void
fuzz_check( fuzz_case_t * c ) {
  FD_TEST( !fd_ghost_verify( c->ghost ) );

  fd_ghost_blk_t * root = fd_ghost_root( c->ghost );
  FD_TEST( root );
  FD_TEST( root->valid );
  FD_TEST( root->slot>=c->last_root_slot );
  c->last_root_slot = root->slot;

  FD_TEST( c->root_idx<c->blk_cnt );
  FD_TEST( c->blk[ c->root_idx ].live );
  FD_TEST( !memcmp( &root->id, &c->blk[ c->root_idx ].id, sizeof(fd_hash_t) ) );
  FD_TEST( fd_ghost_query( c->ghost, &root->id )==root );

  fd_ghost_blk_t * best = fd_ghost_best( c->ghost, root );
  FD_TEST( best );
  FD_TEST( fd_ghost_query( c->ghost, &best->id )==best );
  FD_TEST( !fd_ghost_invalid_ancestor( c->ghost, best ) );

  fd_ghost_blk_t * deepest = fd_ghost_deepest( c->ghost, root );
  FD_TEST( deepest );
  FD_TEST( fd_ghost_query( c->ghost, &deepest->id )==deepest );
  if( FD_UNLIKELY( deepest!=best && fd_ghost_invalid_ancestor( c->ghost, deepest ) ) )
    FD_FUZZ_MUST_BE_COVERED;

  if( FD_UNLIKELY( best==root && fd_ghost_blk_child( c->ghost, root ) ) )
    FD_FUZZ_MUST_BE_COVERED;

  fuzz_expect_stakes( c );
}

static void
fuzz_action_insert( fuzz_case_t *  c,
                    fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( c->blk_cnt>=FUZZ_BLK_MAX ) ) return;

  ulong parent_idx = fuzz_pick_live( c, cur );
  ulong slot       = c->blk[ parent_idx ].slot + 1UL + fuzz_bounded( cur, 3UL );
  (void)fuzz_insert_block( c, parent_idx, slot, cur );

  FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_action_insert_duplicate( fuzz_case_t *  c,
                              fuzz_cursor_t * cur ) {
  if( FD_UNLIKELY( c->blk_cnt>=FUZZ_BLK_MAX ) ) return;

  ulong parent_idx;
  ulong child_idx;
  if( FD_UNLIKELY( !fuzz_pick_duplicate_parent( c, cur, &parent_idx, &child_idx ) ) ) {
    fuzz_action_insert( c, cur );
    return;
  }

  fd_ghost_blk_t * blk = fuzz_insert_block( c, parent_idx, c->blk[ child_idx ].slot, cur );
  FD_TEST( blk );

  fd_ghost_eqvoc( c->ghost, &c->blk[ child_idx ].id );
  fd_ghost_eqvoc( c->ghost, &blk->id );

  FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_action_eqvoc( fuzz_case_t *  c,
                   fuzz_cursor_t * cur ) {
  ulong idx;
  if( FD_UNLIKELY( !fuzz_pick_live_nonroot( c, cur, &idx ) ) ) return;

  fd_ghost_eqvoc( c->ghost, &c->blk[ idx ].id );
  FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_action_confirm( fuzz_case_t *  c,
                     fuzz_cursor_t * cur ) {
  ulong idx = fuzz_pick_live( c, cur );
  fd_ghost_blk_t * before = fd_ghost_query( c->ghost, &c->blk[ idx ].id );
  FD_TEST( before );
  int was_invalid = !before->valid;

  fd_ghost_confirm( c->ghost, &c->blk[ idx ].id );

  fd_ghost_blk_t * after = fd_ghost_query( c->ghost, &c->blk[ idx ].id );
  FD_TEST( after );
  if( FD_UNLIKELY( was_invalid && after->valid ) ) FD_FUZZ_MUST_BE_COVERED;
  FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_action_vote( fuzz_case_t *  c,
                  fuzz_cursor_t * cur,
                  int             edge_slot ) {
  ulong       voter_idx = fuzz_bounded( cur, FUZZ_VOTER_MAX );
  ulong       blk_idx   = fuzz_pick_live( c, cur );
  fd_pubkey_t vote_acc  = fuzz_pubkey( voter_idx );
  ulong       stake     = 1UL + fuzz_bounded( cur, FUZZ_STAKE_MAX );
  ulong       slot      = c->blk[ blk_idx ].slot;

  if( FD_UNLIKELY( edge_slot ) ) {
    switch( fuzz_bounded( cur, 4UL ) ) {
    case 0:
      slot = ULONG_MAX;
      break;
    case 1:
      slot = c->last_root_slot ? c->last_root_slot-1UL : ULONG_MAX;
      break;
    case 2:
      if( c->voter[ voter_idx ].active ) slot = c->voter[ voter_idx ].slot;
      break;
    default:
      break;
    }
  }

  fd_ghost_blk_t * blk = fd_ghost_query( c->ghost, &c->blk[ blk_idx ].id );
  FD_TEST( blk );

  int rc = fd_ghost_count_vote( c->ghost, blk, &vote_acc, stake, slot );
  if( FD_LIKELY( rc==FD_GHOST_SUCCESS ) ) {
    c->voter[ voter_idx ].active  = 1;
    c->voter[ voter_idx ].blk_idx = blk_idx;
    c->voter[ voter_idx ].slot    = slot;
    c->voter[ voter_idx ].stake   = stake;
    FD_FUZZ_MUST_BE_COVERED;
  } else {
    FD_TEST( rc==FD_GHOST_ERR_NOT_VOTED     ||
             rc==FD_GHOST_ERR_VOTE_TOO_OLD  ||
             rc==FD_GHOST_ERR_ALREADY_VOTED );
    FD_FUZZ_MUST_BE_COVERED;
  }
}

static void
fuzz_action_publish( fuzz_case_t *  c,
                     fuzz_cursor_t * cur ) {
  ulong idx;
  if( FD_UNLIKELY( !fuzz_pick_publish_root( c, cur, &idx ) ) ) return;

  fd_ghost_blk_t * blk = fd_ghost_query( c->ghost, &c->blk[ idx ].id );
  FD_TEST( blk );
  fd_ghost_publish( c->ghost, blk );
  fuzz_reconcile_publish( c, idx );

  FD_FUZZ_MUST_BE_COVERED;
}

int
LLVMFuzzerInitialize( int *    argc,
                      char *** argv ) {
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );
  fd_boot( argc, argv );
  fd_log_level_core_set( 3 ); /* crash on warning log */
  fd_log_level_stderr_set( 4 );
  fd_log_level_logfile_set( 4 );

  fuzz_wksp = fd_wksp_new_anonymous( FD_SHMEM_NORMAL_PAGE_SZ,
                                     FUZZ_WKSP_PAGES,
                                     fd_shmem_cpu_idx( 0UL ),
                                     "ghost_fuzz",
                                     0UL );
  FD_TEST( fuzz_wksp );

  fuzz_ghost_mem = fd_wksp_alloc_laddr( fuzz_wksp,
                                        fd_ghost_align(),
                                        fd_ghost_footprint( FUZZ_BLK_MAX, FUZZ_VOTER_MAX ),
                                        1UL );
  FD_TEST( fuzz_ghost_mem );

  atexit( fuzz_cleanup );
  return 0;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {
  fuzz_cursor_t cur = {
    .data    = data,
    .data_sz = size,
    .off     = 0UL,
    .salt    = 0xdecafbad12345678UL ^ size
  };

  fuzz_case_t c;
  memset( &c, 0, sizeof(c) );

  c.mem = fuzz_ghost_mem;

  c.ghost = fd_ghost_join( fd_ghost_new( c.mem, FUZZ_BLK_MAX, FUZZ_VOTER_MAX, cur.salt ) );
  FD_TEST( c.ghost );

  c.blk_cnt        = 1UL;
  c.root_idx       = 0UL;
  c.last_root_slot = 0UL;
  fuzz_hash( &c.blk[ 0 ].id, 0UL, cur.salt );
  c.blk[ 0 ].parent_idx = ULONG_MAX;
  c.blk[ 0 ].slot       = 0UL;
  c.blk[ 0 ].live       = 1;

  FD_TEST( fd_ghost_init( c.ghost, 0UL, c.blk[ 0 ].slot, &c.blk[ 0 ].id ) );

  ulong action_cnt = 1UL + fuzz_bounded( &cur, FUZZ_ACTION_MAX );
  for( ulong i=0UL; i<action_cnt; i++ ) {
    switch( fuzz_bounded( &cur, 7UL ) ) {
    case 0:
      fuzz_action_insert( &c, &cur );
      break;
    case 1:
      fuzz_action_insert_duplicate( &c, &cur );
      break;
    case 2:
      fuzz_action_eqvoc( &c, &cur );
      break;
    case 3:
      fuzz_action_confirm( &c, &cur );
      break;
    case 4:
      fuzz_action_vote( &c, &cur, 0 );
      break;
    case 5:
      fuzz_action_vote( &c, &cur, 1 );
      break;
    default:
      fuzz_action_publish( &c, &cur );
      break;
    }

    fuzz_check( &c );
  }

  fd_ghost_delete( fd_ghost_leave( c.ghost ) );
  FD_FUZZ_MUST_BE_COVERED;
  return 0;
}
