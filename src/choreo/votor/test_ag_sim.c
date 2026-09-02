#include "ag_sim.h"

#define TEST_NV       (5UL)
#define TEST_SLOT_MAX (16UL)
#define TEST_DELAY_NS (10000000L)

static ag_block_id_t
genesis_id( void ) {
  ag_block_id_t genesis = { .slot = 0UL };
  fd_memset( genesis.hash, 0, sizeof(ag_block_hash_t) );
  return genesis;
}

static void
block_hash( ag_block_hash_t out,
            ulong           slot,
            ulong           fork ) {
  fd_memset( out, 0, sizeof(ag_block_hash_t) );
  FD_STORE( ulong, out,      0x626c6f636b000000UL ^ slot );
  FD_STORE( ulong, out+8UL,  0x666f726b00000000UL ^ fork );
  FD_STORE( ulong, out+16UL, fd_ulong_hash( slot ) );
  FD_STORE( ulong, out+24UL, fd_ulong_hash( fork ) );
}

static ag_block_info_t
make_block( ulong                 slot,
            ulong                 fork,
            ag_block_id_t const * parent ) {
  ag_block_info_t block = { .parent = *parent };
  block_hash( block.hash, slot, fork );
  return block;
}

static ag_sim_t *
new_sim( long delay_ns ) {
  ag_sim_cfg_t cfg = ag_sim_cfg_default();
  cfg.validator_cnt    = TEST_NV;
  cfg.slot_max         = TEST_SLOT_MAX;
  cfg.network_delay_ns = delay_ns;
  ag_sim_t * sim = ag_sim_new( &cfg );
  FD_TEST( sim );
  FD_TEST( ag_sim_validator_cnt( sim )==TEST_NV );
  FD_TEST( ag_sim_all_nodes( sim )==((1UL<<TEST_NV)-1UL) );
  for( ulong i=0UL; i<TEST_NV; i++ ) {
    FD_TEST( ag_sim_node_pool      ( sim, i ) );
    FD_TEST( ag_sim_node_votor     ( sim, i ) );
    FD_TEST( ag_sim_node_epoch_info( sim, i )->validator_cnt==TEST_NV );
    FD_TEST( ag_sim_node_now       ( sim, i )==0L );
  }
  return sim;
}

static void
assert_finalized( ag_sim_t * sim,
                  ulong      slot ) {
  for( ulong i=0UL; i<TEST_NV; i++ ) {
    FD_TEST( ag_pool_finalized_slot( ag_sim_node_pool( sim, i ) )==slot );
  }
}

/* Cross-node votes must not arrive before their directed-link deadline. */

static void
test_network_delay( void ) {
  ag_sim_t * sim = new_sim( TEST_DELAY_NS );

  ag_block_id_t   parent = genesis_id();
  ag_block_info_t block  = make_block( 1UL, 0UL, &parent );
  FD_TEST( ag_sim_inject_block( sim, 0L, ag_sim_all_nodes( sim ), 1UL, &block )==AG_SIM_SUCCESS );

  FD_TEST( ag_sim_run( sim )==AG_SIM_SUCCESS );
  assert_finalized( sim, 0UL );

  FD_TEST( ag_sim_run_until( sim, TEST_DELAY_NS-1L )==AG_SIM_SUCCESS );
  assert_finalized( sim, 0UL );

  FD_TEST( ag_sim_run_until( sim, TEST_DELAY_NS )==AG_SIM_SUCCESS );
  assert_finalized( sim, 1UL );
  for( ulong i=0UL; i<TEST_NV; i++ ) {
    FD_TEST( ag_sim_node_now( sim, i )==TEST_DELAY_NS );
    FD_TEST( ag_sim_node_stats( sim, i )->vote_recv_cnt>=TEST_NV );
    FD_TEST( ag_sim_node_stats( sim, i )->vote_emit_cnt==2UL ); /* notar + final, no fallback/skip */
  }

  FD_TEST( ag_sim_run_until( sim, 2L*TEST_DELAY_NS )==AG_SIM_SUCCESS );
  FD_TEST( ag_sim_stats( sim )->network_delivery_cnt>0UL );
  ag_sim_delete( sim );
}

struct sim_result {
  ag_sim_stats_t      stats;
  ag_sim_node_stats_t node[ TEST_NV ];
  ulong               finalized[ TEST_NV ];
};
typedef struct sim_result sim_result_t;

static sim_result_t
run_chain( void ) {
  ag_sim_t * sim = new_sim( 1000000L );

  ag_block_id_t parent = genesis_id();
  for( ulong slot=1UL; slot<=8UL; slot++ ) {
    ag_block_info_t block = make_block( slot, 0UL, &parent );
    FD_TEST( ag_sim_inject_block( sim, 0L, ag_sim_all_nodes( sim ), slot, &block )==AG_SIM_SUCCESS );
    parent.slot = slot;
    fd_memcpy( parent.hash, block.hash, sizeof(ag_block_hash_t) );
  }

  FD_TEST( ag_sim_run_until( sim, 20000000L )==AG_SIM_SUCCESS );
  assert_finalized( sim, 8UL );

  sim_result_t result = { .stats = *ag_sim_stats( sim ) };
  for( ulong i=0UL; i<TEST_NV; i++ ) {
    result.node[i]      = *ag_sim_node_stats( sim, i );
    result.finalized[i] = ag_pool_finalized_slot( ag_sim_node_pool( sim, i ) );
    FD_TEST( result.node[i].completed_block_cnt==8UL );
    FD_TEST( result.node[i].vote_emit_cnt>0UL );
    FD_TEST( result.node[i].cert_emit_cnt>0UL );
  }

  ag_sim_delete( sim );
  return result;
}

/* Hash maps use different per-node seeds, but identical simulator inputs must
   still produce byte-for-byte identical observable state.  The chain crosses
   two leader-window boundaries, exercising pending blocks/parent-ready. */

static void
test_deterministic_chained_consensus( void ) {
  sim_result_t a = run_chain();
  sim_result_t b = run_chain();
  FD_TEST( fd_memeq( &a, &b, sizeof(sim_result_t) ) );
}

static void
test_dead_block( void ) {
  ag_sim_t * sim = new_sim( 1000000L );
  FD_TEST( ag_sim_inject_dead( sim, 0L, ag_sim_all_nodes( sim ), 1UL )==AG_SIM_SUCCESS );
  FD_TEST( ag_sim_run_until( sim, 5000000L )==AG_SIM_SUCCESS );

  assert_finalized( sim, 0UL );
  for( ulong i=0UL; i<TEST_NV; i++ ) {
    ag_sim_node_stats_t const * stats = ag_sim_node_stats( sim, i );
    FD_TEST( stats->dead_block_cnt==1UL );
    FD_TEST( stats->vote_emit_cnt>=AG_SLOTS_PER_WINDOW-1UL );
    FD_TEST( stats->cert_emit_cnt>0UL );
  }
  ag_sim_delete( sim );
}

static void
test_virtual_timeouts( void ) {
  ag_sim_t * sim = new_sim( 0L );

  long crashed_leader = AG_DELTA_TIMEOUT_NS + AG_DELTA_FIRST_SLICE_NS;
  FD_TEST( ag_sim_run_until( sim, crashed_leader-1L )==AG_SIM_SUCCESS );
  for( ulong i=0UL; i<TEST_NV; i++ ) FD_TEST( !ag_sim_node_stats( sim, i )->timeout_event_cnt );

  FD_TEST( ag_sim_run_until( sim, crashed_leader )==AG_SIM_SUCCESS );
  for( ulong i=0UL; i<TEST_NV; i++ ) FD_TEST( ag_sim_node_stats( sim, i )->timeout_event_cnt==1UL );

  /* set_timeouts arms the ordinary timeout for slot 1 after the crashed
     leader timeout and the slot-0 timeout.  Once it fires, every validator
     votes to skip each non-genesis slot in the first window. */
  long slot_one_timeout = AG_DELTA_TIMEOUT_NS + AG_DELTA_FIRST_SLICE_NS +
                          (AG_DELTA_BLOCK_NS-AG_DELTA_FIRST_SLICE_NS) +
                          AG_DELTA_BLOCK_NS;
  FD_TEST( ag_sim_run_until( sim, slot_one_timeout )==AG_SIM_SUCCESS );
  for( ulong i=0UL; i<TEST_NV; i++ ) {
    ag_sim_node_stats_t const * stats = ag_sim_node_stats( sim, i );
    FD_TEST( stats->timeout_event_cnt==3UL );
    FD_TEST( stats->vote_emit_cnt>=AG_SLOTS_PER_WINDOW-1UL );
  }
  ag_sim_delete( sim );
}

static void
test_link_partition( void ) {
  ag_sim_t * sim = new_sim( 0L );
  for( ulong peer=0UL; peer<TEST_NV; peer++ ) {
    if( peer==TEST_NV-1UL ) continue;
    FD_TEST( ag_sim_set_link_delay( sim, TEST_NV-1UL, peer, LONG_MAX )==AG_SIM_SUCCESS );
    FD_TEST( ag_sim_set_link_delay( sim, peer, TEST_NV-1UL, LONG_MAX )==AG_SIM_SUCCESS );
  }

  ag_block_id_t   parent = genesis_id();
  ag_block_info_t block  = make_block( 1UL, 0UL, &parent );
  FD_TEST( ag_sim_inject_block( sim, 0L, ag_sim_all_nodes( sim ), 1UL, &block )==AG_SIM_SUCCESS );
  FD_TEST( ag_sim_run( sim )==AG_SIM_SUCCESS );

  /* Four of five equal-stake validators meet the strong (80%) quorum. */
  for( ulong i=0UL; i<TEST_NV-1UL; i++ ) {
    FD_TEST( ag_pool_finalized_slot( ag_sim_node_pool( sim, i ) )==1UL );
  }
  FD_TEST( ag_pool_finalized_slot( ag_sim_node_pool( sim, TEST_NV-1UL ) )==0UL );
  FD_TEST( ag_sim_stats( sim )->network_drop_cnt>0UL );
  ag_sim_delete( sim );
}

static void
test_max_validator_count( void ) {
  ag_sim_cfg_t cfg = ag_sim_cfg_default();
  cfg.validator_cnt    = AG_SIM_VALIDATOR_MAX;
  cfg.slot_max         = AG_SLOTS_PER_WINDOW;
  cfg.network_delay_ns = 0L;
  ag_sim_t * sim = ag_sim_new( &cfg );
  FD_TEST( sim );

  ag_block_id_t   parent = genesis_id();
  ag_block_info_t block  = make_block( 1UL, 0UL, &parent );
  FD_TEST( ag_sim_inject_block( sim, 0L, ag_sim_all_nodes( sim ), 1UL, &block )==AG_SIM_SUCCESS );
  FD_TEST( ag_sim_run( sim )==AG_SIM_SUCCESS );
  for( ulong i=0UL; i<AG_SIM_VALIDATOR_MAX; i++ ) {
    FD_TEST( ag_pool_finalized_slot( ag_sim_node_pool( sim, i ) )==1UL );
    FD_TEST( ag_sim_node_epoch_info( sim, i )->validator_cnt==AG_SIM_VALIDATOR_MAX );
  }
  ag_sim_delete( sim );
}

int
main( int     argc,
      char ** argv ) {
  fd_boot( &argc, &argv );

  int stderr_level = fd_log_level_stderr();
  if( stderr_level<4 ) fd_log_level_stderr_set( 4 );

  test_network_delay();
  test_deterministic_chained_consensus();
  test_dead_block();
  test_virtual_timeouts();
  test_link_partition();
  test_max_validator_count();

  fd_log_level_stderr_set( stderr_level );
  FD_LOG_NOTICE(( "pass" ));
  fd_halt();
  return 0;
}
