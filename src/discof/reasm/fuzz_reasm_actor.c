#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include <stdlib.h>
#include <string.h>

#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"
#include "fd_reasm.h"
#include "fd_reasm_private.h"

/* This is a metadata-level actor fuzzer for fd_reasm_t.  Raw shred
   receive is not exposed by the reasm API, so the program drives the
   same FEC metadata operations used by replay: insert, confirm, pop,
   remove, and publish. */

#define FUZZ_FEC_MAX   (16UL)
#define FUZZ_NODE_MAX  (26UL)
#define FUZZ_OP_MAX    (96UL)
#define FUZZ_WKSP_PG   (256UL)

#define FUZZ_OP_INSERT  0U
#define FUZZ_OP_CONFIRM 1U
#define FUZZ_OP_POP     2U
#define FUZZ_OP_REMOVE  3U
#define FUZZ_OP_PUBLISH 4U
#define FUZZ_OP_QUERY   5U
#define FUZZ_OP_DRAIN   6U
#define FUZZ_OP_CNT     7U
#define FUZZ_PARENT_ROOT ((int)-1)
#define FUZZ_PARENT_FAKE ((int)-2)

typedef struct {
  uchar const * data;
  ulong         data_sz;
  ulong         data_off;
} fuzz_cursor_t;

typedef struct {
  int    parent;
  ulong  slot;
  uint   fec_set_idx;
  ushort parent_off;
  ushort data_cnt;
  uchar  data_complete;
  uchar  slot_complete;
  uchar  is_leader;
  uchar  expect_invalid_if_parent_present;
} fuzz_node_desc_t;

typedef struct {
  fd_hash_t key[1];
  fd_hash_t cmr[1];
  ulong     insert_attempt_cnt;
  int       ever_present;
  int       present;
  int       dropped;
  int       popped;
  int       confirmed;
  int       replayable;
} fuzz_node_t;

typedef struct {
  fuzz_node_t node[ FUZZ_NODE_MAX ];
  ulong       duplicate_cnt;
  ulong       invalid_cnt;
  ulong       orphan_cnt;
  ulong       dropped_cnt;
  ulong       replayable_cnt;
  ulong       pop_cnt;
  ulong       remove_cnt;
  ulong       publish_cnt;
  ulong       eviction_cnt;
  ulong       eqvoc_cnt;
} fuzz_model_t;

static fd_wksp_t * fuzz_wksp;
static void *      fuzz_reasm_mem;

static fuzz_node_desc_t const fuzz_desc[ FUZZ_NODE_MAX ] = {
  /* parent,           slot, fec_idx, parent_off, data_cnt, dc, sc, ldr, invalid */
  { FUZZ_PARENT_ROOT,  1UL,  0U,      1U,         32U,      0U, 0U, 0U, 0U },
  { 0,                 1UL,  32U,     1U,         32U,      0U, 0U, 0U, 0U },
  { 1,                 1UL,  64U,     1U,         32U,      1U, 1U, 0U, 0U },
  { 2,                 2UL,  0U,      1U,         32U,      0U, 0U, 0U, 0U },
  { 3,                 2UL,  32U,     1U,         32U,      0U, 0U, 0U, 0U },
  { 4,                 2UL,  64U,     1U,         32U,      1U, 1U, 0U, 0U },
  { 2,                 3UL,  0U,      2U,         32U,      0U, 0U, 0U, 0U },
  { 6,                 3UL,  32U,     2U,         32U,      1U, 1U, 0U, 0U },
  { 5,                 4UL,  0U,      2U,         32U,      0U, 0U, 0U, 0U },
  { 8,                 4UL,  32U,     2U,         32U,      1U, 1U, 0U, 0U },

  /* Alternate slot 1 chain with the same (slot,fec_set_idx) values to
     exercise equivocation and confirmation backfill. */
  { FUZZ_PARENT_ROOT,  1UL,  0U,      1U,         32U,      0U, 0U, 0U, 0U },
  { 10,                1UL,  32U,     1U,         32U,      0U, 0U, 0U, 0U },
  { 11,                1UL,  64U,     1U,         32U,      1U, 1U, 0U, 0U },
  { 12,                5UL,  0U,      4U,         32U,      1U, 1U, 0U, 0U },

  /* Invalid when the referenced parent is present.  If inserted
     before its parent, reasm should hold it as an orphan and drop it
     when the bad chain becomes checkable. */
  { 2,                 1UL,  96U,     1U,         32U,      0U, 0U, 0U, 1U },
  { 2,                 2UL,  32U,     1U,         32U,      0U, 0U, 0U, 1U },
  { 1,                 1UL,  64U,     2U,         32U,      0U, 0U, 0U, 1U },
  { 1,                 2UL,  0U,      1U,         32U,      0U, 0U, 0U, 1U },

  /* Backfill-like chain.  The fuzzer can insert 20 last, after 18 and
     19 are already orphaned, to connect the whole chain. */
  { 19,                6UL,  64U,     5U,         32U,      1U, 1U, 0U, 0U },
  { 20,                6UL,  32U,     5U,         32U,      0U, 0U, 0U, 0U },
  { 2,                 6UL,  0U,      5U,         32U,      0U, 0U, 0U, 0U },

  /* Fork and same-xid fork off a later slot. */
  { 9,                 7UL,  0U,      3U,         32U,      1U, 1U, 0U, 0U },
  { 9,                 7UL,  0U,      3U,         32U,      1U, 1U, 0U, 0U },

  /* Orphan subtree that usually never connects, plus a child that
     becomes invalid if its slot-complete parent appears. */
  { 24,                8UL,  32U,     1U,         32U,      1U, 1U, 1U, 0U },
  { FUZZ_PARENT_FAKE,  8UL,  0U,      1U,         32U,      0U, 0U, 1U, 0U },
  { 23,                8UL,  64U,     1U,         32U,      0U, 0U, 1U, 1U },
};

static void
fuzz_fini( void ) {
  if( FD_LIKELY( fuzz_wksp ) ) {
    fd_wksp_delete_anonymous( fuzz_wksp );
    fuzz_wksp = NULL;
  }
  fd_halt();
}

int
LLVMFuzzerInitialize( int  *   argc,
                      char *** argv ) {
  putenv( "FD_LOG_BACKTRACE=0" );
  setenv( "FD_LOG_PATH", "", 0 );
  fd_boot( argc, argv );
  fd_log_level_core_set( 3 ); /* crash on warning log */
  fd_log_level_stderr_set( 4 );
  fd_log_level_logfile_set( 4 );

  fuzz_wksp = fd_wksp_new_anonymous( FD_SHMEM_NORMAL_PAGE_SZ,
                                     FUZZ_WKSP_PG,
                                     fd_shmem_cpu_idx( 0UL ),
                                     "reasm_fuzz",
                                     0UL );
  FD_TEST( fuzz_wksp );
  fuzz_reasm_mem = fd_wksp_alloc_laddr( fuzz_wksp,
                                        fd_reasm_align(),
                                        fd_reasm_footprint( FUZZ_FEC_MAX ),
                                        1UL );
  FD_TEST( fuzz_reasm_mem );
  atexit( fuzz_fini );
  return 0;
}

static uchar
fuzz_fallback_u8( fuzz_cursor_t const * cur ) {
  ulong h = fd_ulong_hash( cur->data_off ^
                           (cur->data_sz<<1) ^
                           0x91fce7c4a1d09b35UL );
  return (uchar)h;
}

static uchar
fuzz_u8( fuzz_cursor_t * cur ) {
  if( FD_LIKELY( cur->data_off<cur->data_sz ) )
    return cur->data[ cur->data_off++ ];

  cur->data_off++;
  return fuzz_fallback_u8( cur );
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
fuzz_hash( fd_hash_t * out,
           ulong       id ) {
  for( ulong i=0UL; i<4UL; i++ )
    out->ul[ i ] = 0x9e3779b97f4a7c15UL*(id+i+1UL) ^
                   (0xd1b54a32d192ed03UL + (id<<17));
}

static void
fuzz_model_init( fuzz_model_t * model,
                 fd_hash_t const * root_key ) {
  fd_memset( model, 0, sizeof(fuzz_model_t) );

  for( ulong i=0UL; i<FUZZ_NODE_MAX; i++ ) {
    fuzz_hash( model->node[ i ].key, 1000UL+i );
    if( fuzz_desc[ i ].parent==FUZZ_PARENT_ROOT ) {
      *model->node[ i ].cmr = *root_key;
    } else if( fuzz_desc[ i ].parent==FUZZ_PARENT_FAKE ) {
      fuzz_hash( model->node[ i ].cmr, 9000UL+i );
    } else {
      *model->node[ i ].cmr = *model->node[ (ulong)fuzz_desc[ i ].parent ].key;
    }
  }
}

static int
fuzz_connected( fd_reasm_t *     reasm,
                fd_reasm_fec_t * fec ) {
  fd_reasm_fec_t * root = fd_reasm_root( reasm );
  for( ulong depth=0UL; FD_LIKELY( fec && depth<=FUZZ_FEC_MAX ); depth++ ) {
    if( FD_LIKELY( fec==root ) ) return 1;
    fec = fd_reasm_parent( reasm, fec );
  }
  return 0;
}

static void
fuzz_model_refresh( fuzz_model_t * model,
                    fd_reasm_t *   reasm ) {
  model->dropped_cnt    = 0UL;
  model->replayable_cnt = 0UL;
  model->eqvoc_cnt      = 0UL;

  for( ulong i=0UL; i<FUZZ_NODE_MAX; i++ ) {
    fuzz_node_t *    node = &model->node[ i ];
    fd_reasm_fec_t * fec  = fd_reasm_query( reasm, node->key );

    if( FD_UNLIKELY( !fec ) ) {
      if( FD_UNLIKELY( node->present ) ) {
        node->dropped = 1;
        FD_FUZZ_MUST_BE_COVERED;
      }
      node->present    = 0;
      node->replayable = 0;
      if( node->dropped ) model->dropped_cnt++;
      continue;
    }

    node->ever_present = 1;
    node->present      = 1;
    node->dropped      = 0;
    node->popped       = node->popped    || !!fec->popped;
    node->confirmed    = node->confirmed || !!fec->confirmed;
    node->replayable   = !!fec->in_out && !fec->popped &&
                         ( !fec->eqvoc || fec->confirmed ) &&
                         fuzz_connected( reasm, fec );
    if( node->replayable ) model->replayable_cnt++;
    if( fec->eqvoc )       model->eqvoc_cnt++;
  }
}

static void
fuzz_release_chain( fd_reasm_t *     reasm,
                    fd_reasm_fec_t * head ) {
  while( FD_LIKELY( head ) ) {
    fd_reasm_fec_t * next = fd_reasm_child( reasm, head );
    fd_reasm_pool_release( reasm, head );
    head = next;
  }
}

static void
fuzz_verify_out( fd_reasm_t * reasm ) {
  fd_reasm_fec_t * pool = reasm_pool( reasm );

  ulong out_cnt = 0UL;
  fd_reasm_fec_t * expect_peek = NULL;
  for( out_iter_t iter = out_iter_fwd_init( reasm->out, pool );
       !out_iter_done( iter, reasm->out, pool );
       iter = out_iter_fwd_next( iter, reasm->out, pool ) ) {
    fd_reasm_fec_t * fec = out_iter_ele( iter, reasm->out, pool );
    FD_TEST( fec->in_out );
    FD_TEST( ancestry_ele_query( reasm->ancestry, &fec->key, NULL, pool ) ||
             frontier_ele_query( reasm->frontier, &fec->key, NULL, pool ) );
    if( FD_UNLIKELY( !expect_peek &&
                     !fec->popped &&
                     ( !fec->eqvoc || fec->confirmed ) ) )
      expect_peek = fec;
    out_cnt++;
  }

  ulong in_out_cnt = 0UL;
  for( ancestry_iter_t iter = ancestry_iter_init( reasm->ancestry, pool );
       !ancestry_iter_done( iter, reasm->ancestry, pool );
       iter = ancestry_iter_next( iter, reasm->ancestry, pool ) ) {
    fd_reasm_fec_t * fec = ancestry_iter_ele( iter, reasm->ancestry, pool );
    if( fec->in_out ) in_out_cnt++;
  }
  for( frontier_iter_t iter = frontier_iter_init( reasm->frontier, pool );
       !frontier_iter_done( iter, reasm->frontier, pool );
       iter = frontier_iter_next( iter, reasm->frontier, pool ) ) {
    fd_reasm_fec_t * fec = frontier_iter_ele( iter, reasm->frontier, pool );
    if( fec->in_out ) in_out_cnt++;
  }

  FD_TEST( in_out_cnt==out_cnt );
  FD_TEST( fd_reasm_peek( reasm )==expect_peek );
}

static void
fuzz_verify( fuzz_model_t * model,
             fd_reasm_t *   reasm ) {
  FD_TEST( fd_reasm_root( reasm ) );
  fuzz_verify_out( reasm );
  fuzz_model_refresh( model, reasm );

  if( FD_UNLIKELY( model->replayable_cnt ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( model->dropped_cnt    ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( model->eqvoc_cnt      ) ) FD_FUZZ_MUST_BE_COVERED;
}

static ulong
fuzz_pick_node( fuzz_cursor_t * cur ) {
  return fuzz_bounded( cur, FUZZ_NODE_MAX );
}

static fd_reasm_fec_t *
fuzz_pick_slot_complete_present( fuzz_cursor_t * cur,
                                 fuzz_model_t *  model,
                                 fd_reasm_t *    reasm,
                                 int             require_connected,
                                 int             exclude_root ) {
  ulong start = fuzz_pick_node( cur );
  fd_reasm_fec_t * root = fd_reasm_root( reasm );

  for( ulong j=0UL; j<FUZZ_NODE_MAX; j++ ) {
    ulong i = (start+j) % FUZZ_NODE_MAX;
    if( FD_UNLIKELY( !fuzz_desc[ i ].slot_complete ) ) continue;
    fd_reasm_fec_t * fec = fd_reasm_query( reasm, model->node[ i ].key );
    if( FD_UNLIKELY( !fec ) ) continue;
    if( FD_UNLIKELY( exclude_root && fec==root ) ) continue;
    if( FD_UNLIKELY( require_connected && !fuzz_connected( reasm, fec ) ) ) continue;
    return fec;
  }

  return NULL;
}

static fd_reasm_fec_t *
fuzz_pick_removable( fuzz_cursor_t * cur,
                     fuzz_model_t *  model,
                     fd_reasm_t *    reasm ) {
  fd_reasm_fec_t * pool = reasm_pool( reasm );
  ulong start = fuzz_pick_node( cur );
  fd_reasm_fec_t * root = fd_reasm_root( reasm );

  for( ulong j=0UL; j<FUZZ_NODE_MAX; j++ ) {
    ulong i = (start+j) % FUZZ_NODE_MAX;
    fd_reasm_fec_t * fec = fd_reasm_query( reasm, model->node[ i ].key );
    if( FD_UNLIKELY( !fec || fec==root ) ) continue;
    if( FD_UNLIKELY( fd_reasm_child( reasm, fec ) ) ) continue;

    int orphan_tree = !!orphaned_ele_query( reasm->orphaned, &fec->key, NULL, pool ) ||
                      !!subtrees_ele_query( reasm->subtrees, &fec->key, NULL, pool );
    if( FD_UNLIKELY( !orphan_tree && ( !fec->popped || !fuzz_connected( reasm, fec ) ) ) ) continue;
    if( FD_UNLIKELY( !orphan_tree && fec->fec_set_idx && !fd_reasm_parent( reasm, fec ) ) ) continue;
    return fec;
  }

  return NULL;
}

static void
fuzz_insert( fuzz_cursor_t * cur,
             fuzz_model_t *  model,
             fd_reasm_t *    reasm ) {
  ulong i = fuzz_pick_node( cur );
  fuzz_node_desc_t const * desc = &fuzz_desc[ i ];
  fuzz_node_t * node = &model->node[ i ];

  node->insert_attempt_cnt++;

  if( FD_UNLIKELY( fd_reasm_query( reasm, node->key ) ) ) {
    model->duplicate_cnt++;
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  fd_reasm_fec_t * evicted = NULL;
  fd_reasm_fec_t * inserted =
    fd_reasm_insert( reasm,
                     node->key,
                     node->cmr,
                     desc->slot,
                     desc->fec_set_idx,
                     desc->parent_off,
                     desc->data_cnt,
                     !!desc->data_complete,
                     !!desc->slot_complete,
                     !!desc->is_leader,
                     NULL,
                     &evicted );

  if( FD_UNLIKELY( evicted ) ) {
    model->eviction_cnt++;
    FD_FUZZ_MUST_BE_COVERED;
    fuzz_release_chain( reasm, evicted );
  }

  if( FD_LIKELY( inserted ) ) {
    FD_TEST( fd_reasm_query( reasm, node->key )==inserted );
    node->present      = 1;
    node->ever_present = 1;
    node->dropped      = 0;
    node->popped       = 0;
    node->confirmed    = 0;

    if( FD_UNLIKELY( subtrees_ele_query( reasm->subtrees,
                                         node->key,
                                         NULL,
                                         reasm_pool( reasm ) ) ) ) {
      model->orphan_cnt++;
      FD_FUZZ_MUST_BE_COVERED;
    }
    if( FD_UNLIKELY( inserted->eqvoc ) ) FD_FUZZ_MUST_BE_COVERED;
  } else {
    FD_TEST( !fd_reasm_query( reasm, node->key ) );
    model->invalid_cnt++;
    if( desc->expect_invalid_if_parent_present ) FD_FUZZ_MUST_BE_COVERED;
  }
}

static void
fuzz_confirm( fuzz_cursor_t * cur,
              fuzz_model_t *  model,
              fd_reasm_t *    reasm ) {
  if( FD_UNLIKELY( fuzz_u8( cur ) & 1U ) ) {
    fd_hash_t fake[1];
    fuzz_hash( fake, 12000UL + fuzz_bounded( cur, 64UL ) );
    fd_reasm_confirm( reasm, fake );
    return;
  }

  fd_reasm_fec_t * fec = fuzz_pick_slot_complete_present( cur, model, reasm, 1, 0 );
  if( FD_UNLIKELY( !fec ) ) return;

  fd_hash_t key = fec->key;
  fd_reasm_confirm( reasm, &key );
  if( FD_UNLIKELY( fd_reasm_query( reasm, &key ) ) )
    FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_pop_one( fuzz_model_t * model,
              fd_reasm_t *   reasm ) {
  int had_out = !out_is_empty( reasm->out, reasm_pool( reasm ) );
  fd_reasm_fec_t * expected = fd_reasm_peek( reasm );
  fd_reasm_fec_t * popped   = fd_reasm_pop ( reasm );
  FD_TEST( popped==expected );

  if( FD_LIKELY( popped ) ) {
    model->pop_cnt++;
    popped->bank_idx = model->pop_cnt;
    popped->bank_seq = model->pop_cnt;
    FD_FUZZ_MUST_BE_COVERED;
    return;
  }

  if( FD_UNLIKELY( had_out ) ) FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_remove( fuzz_cursor_t * cur,
             fuzz_model_t *  model,
             fd_reasm_t *    reasm ) {
  fd_reasm_fec_t * head = fuzz_pick_removable( cur, model, reasm );
  if( FD_UNLIKELY( !head ) ) return;

  fd_reasm_fec_t * evicted = fd_reasm_remove( reasm, head, NULL );
  FD_TEST( evicted );
  model->remove_cnt++;
  FD_FUZZ_MUST_BE_COVERED;
  fuzz_release_chain( reasm, evicted );
}

static void
fuzz_publish( fuzz_cursor_t * cur,
              fuzz_model_t *  model,
              fd_reasm_t *    reasm ) {
  if( FD_UNLIKELY( model->remove_cnt || model->eviction_cnt ) ) return;

  fd_reasm_fec_t * old_root = fd_reasm_root( reasm );
  if( FD_UNLIKELY( !xid_query( reasm->xid, (old_root->slot << 32)|old_root->fec_set_idx, NULL ) ) ) return;

  fd_reasm_fec_t * fec = fuzz_pick_slot_complete_present( cur, model, reasm, 1, 1 );
  if( FD_UNLIKELY( !fec ) ) return;
  if( FD_UNLIKELY( !fec->popped ) ) return;

  fd_hash_t key = fec->key;
  fd_reasm_fec_t * root = fd_reasm_publish( reasm, &key, NULL );
  FD_TEST( root );
  FD_TEST( fd_hash_eq( &root->key, &key ) );
  model->publish_cnt++;
  FD_FUZZ_MUST_BE_COVERED;
}

static void
fuzz_query( fuzz_cursor_t * cur,
            fuzz_model_t *  model,
            fd_reasm_t *    reasm ) {
  if( FD_UNLIKELY( fuzz_u8( cur ) & 1U ) ) {
    fd_hash_t fake[1];
    fuzz_hash( fake, 13000UL + fuzz_bounded( cur, 64UL ) );
    FD_TEST( !fd_reasm_query( reasm, fake ) );
    return;
  }

  ulong i = fuzz_pick_node( cur );
  fd_reasm_fec_t * fec = fd_reasm_query( reasm, model->node[ i ].key );
  if( FD_UNLIKELY( fec ) ) {
    FD_TEST( fd_hash_eq( &fec->key, model->node[ i ].key ) );
    FD_FUZZ_MUST_BE_COVERED;
  }
}

static void
run_xid_evict_seed( void ) {
  fd_reasm_fec_t * ev[1];
  fd_reasm_t * reasm =
    fd_reasm_join( fd_reasm_new( fuzz_reasm_mem, FUZZ_FEC_MAX, 0UL ) );
  FD_TEST( reasm );

  fd_hash_t mr0[1] = {{{ 1UL, 0UL }}};
  fd_reasm_init( reasm, mr0, 0UL );

  fd_hash_t mr1[1] = {{{ 1UL, 1UL }}};
  fd_hash_t mr2[1] = {{{ 1UL, 2UL }}};
  fd_hash_t mr3[1] = {{{ 1UL, 3UL }}};
  fd_hash_t mr4[1] = {{{ 1UL, 4UL }}};

  fd_reasm_insert( reasm, mr1, mr0, 1UL, 0U,  1U, 32U, 0, 0, 0, NULL, ev );
  fd_reasm_insert( reasm, mr2, mr1, 1UL, 32U, 1U, 32U, 0, 0, 0, NULL, ev );
  fd_reasm_insert( reasm, mr3, mr2, 1UL, 64U, 1U, 32U, 0, 1, 0, NULL, ev );
  fd_reasm_fec_t * fec4 =
    fd_reasm_insert( reasm, mr4, mr2, 1UL, 64U, 1U, 32U, 0, 1, 0, NULL, ev );

  ulong last_xid = (1UL << 32) | 64UL;
  FD_TEST( xid_query( reasm->xid, last_xid, NULL )->cnt==2UL );

  fd_reasm_confirm( reasm, mr4 );
  FD_TEST( xid_query( reasm->xid, last_xid, NULL )->idx==pool_idx( reasm_pool( reasm ), fec4 ) );

  fd_reasm_publish( reasm, mr4, NULL );
  FD_TEST( xid_query( reasm->xid, last_xid, NULL )->cnt==1UL );
  FD_TEST( xid_query( reasm->xid, last_xid, NULL )->idx==pool_idx( reasm_pool( reasm ), fec4 ) );

  fd_reasm_delete( fd_reasm_leave( reasm ) );

  reasm = fd_reasm_join( fd_reasm_new( fuzz_reasm_mem, FUZZ_FEC_MAX, 0UL ) );
  FD_TEST( reasm );

  fd_hash_t mra[1] = {{{ 2UL, 0UL }}};
  fd_reasm_init( reasm, mra, 0UL );

  fd_hash_t mrb[1] = {{{ 2UL, 1UL }}};
  fd_hash_t mrc[1] = {{{ 2UL, 2UL }}};
  fd_hash_t mrd[1] = {{{ 2UL, 3UL }}};
  fd_hash_t mre[1] = {{{ 2UL, 4UL }}};
  fd_hash_t mrf[1] = {{{ 2UL, 5UL }}};
  fd_hash_t mrg[1] = {{{ 2UL, 6UL }}};

  fd_reasm_insert( reasm, mrb, mra, 1UL, 0U,  1U, 32U, 0, 0, 0, NULL, ev );
  fd_reasm_insert( reasm, mrc, mrb, 1UL, 32U, 1U, 32U, 0, 0, 0, NULL, ev );
  fd_reasm_insert( reasm, mre, mrc, 1UL, 64U, 1U, 32U, 0, 1, 0, NULL, ev );
  fd_reasm_fec_t * fecd =
    fd_reasm_insert( reasm, mrd, mrc, 1UL, 64U, 1U, 32U, 0, 1, 0, NULL, ev );
  fd_reasm_fec_t * fecf =
    fd_reasm_insert( reasm, mrf, mrc, 1UL, 64U, 1U, 32U, 0, 1, 0, NULL, ev );

  ulong xid2 = (1UL << 32) | 64UL;
  FD_TEST( xid_query( reasm->xid, xid2, NULL )->cnt==3UL );

  fd_reasm_confirm( reasm, mrd );
  FD_TEST( xid_query( reasm->xid, xid2, NULL )->idx==pool_idx( reasm_pool( reasm ), fecf ) );

  fd_reasm_remove( reasm, fecf, NULL );
  fd_reasm_pool_release( reasm, fecf );
  FD_TEST( xid_query( reasm->xid, xid2, NULL )->cnt==2UL );
  FD_TEST( xid_query( reasm->xid, xid2, NULL )->idx==pool_idx( reasm_pool( reasm ), fecd ) );

  fd_reasm_insert( reasm, mrg, mrd, 2UL, 0U, 1U, 32U, 0, 1, 0, NULL, ev );
  fd_reasm_publish( reasm, mrg, NULL );
  FD_TEST( !xid_query( reasm->xid, xid2, NULL ) );

  fd_reasm_delete( fd_reasm_leave( reasm ) );
  FD_FUZZ_MUST_BE_COVERED;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {
  if( FD_UNLIKELY( size && data[ 0 ]==0xf0U ) ) {
    run_xid_evict_seed();
    return 0;
  }

  fuzz_cursor_t cur = { .data = data, .data_sz = size, .data_off = 0UL };

  fd_hash_t root_key[1];
  fuzz_hash( root_key, 1UL + fuzz_bounded( &cur, 8UL ) );

  fd_reasm_t * reasm =
    fd_reasm_join( fd_reasm_new( fuzz_reasm_mem,
                                 FUZZ_FEC_MAX,
                                 fuzz_bounded( &cur, 1024UL ) ) );
  FD_TEST( reasm );
  FD_TEST( fd_reasm_init( reasm, root_key, 0UL ) );
  FD_TEST( fd_reasm_root( reasm ) );

  fuzz_model_t model[1];
  fuzz_model_init( model, root_key );
  fuzz_verify( model, reasm );

  ulong op_cnt = 1UL + fuzz_bounded( &cur, FUZZ_OP_MAX );
  for( ulong op_idx=0UL; op_idx<op_cnt; op_idx++ ) {
    switch( fuzz_u8( &cur ) % FUZZ_OP_CNT ) {
      case FUZZ_OP_INSERT:  fuzz_insert ( &cur, model, reasm ); break;
      case FUZZ_OP_CONFIRM: fuzz_confirm( &cur, model, reasm ); break;
      case FUZZ_OP_POP:     fuzz_pop_one(       model, reasm ); break;
      case FUZZ_OP_REMOVE:  fuzz_remove ( &cur, model, reasm ); break;
      case FUZZ_OP_PUBLISH: fuzz_publish( &cur, model, reasm ); break;
      case FUZZ_OP_QUERY:   fuzz_query  ( &cur, model, reasm ); break;
      case FUZZ_OP_DRAIN:
        for( ulong i=0UL; i<4UL && fd_reasm_peek( reasm ); i++ )
          fuzz_pop_one( model, reasm );
        break;
      default: break;
    }
    fuzz_verify( model, reasm );
  }

  while( FD_LIKELY( fd_reasm_peek( reasm ) ) ) {
    fuzz_pop_one( model, reasm );
    fuzz_verify( model, reasm );
  }

  if( FD_UNLIKELY( model->duplicate_cnt ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( model->invalid_cnt   ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( model->orphan_cnt    ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( model->pop_cnt       ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( model->remove_cnt    ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( model->publish_cnt   ) ) FD_FUZZ_MUST_BE_COVERED;
  if( FD_UNLIKELY( model->eviction_cnt  ) ) FD_FUZZ_MUST_BE_COVERED;

  fd_reasm_delete( fd_reasm_leave( reasm ) );
  return 0;
}
