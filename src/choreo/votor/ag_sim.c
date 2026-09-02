#include "ag_sim.h"

#include <stdlib.h>

#define AG_SIM_MSG_VOTE (0)
#define AG_SIM_MSG_CERT (1)

#define AG_SIM_INPUT_COMPLETED (0)
#define AG_SIM_INPUT_DEAD      (1)

/* Leave enough signed-time headroom for set_timeouts to arm a complete
   leader window without overflowing. */
#define AG_SIM_TIME_MAX (LONG_MAX - AG_DELTA_TIMEOUT_NS - AG_DELTA_FIRST_SLICE_NS - \
                         (long)(AG_SLOTS_PER_WINDOW+1UL)*AG_DELTA_BLOCK_NS)

struct ag_sim_msg {
  int   kind;
  ulong seq;
  long  ts;
  union {
    ag_vote_t vote;
    ag_cert_t cert;
  } inner;
};
typedef struct ag_sim_msg ag_sim_msg_t;

struct ag_sim_msg_queue {
  ag_sim_msg_t * msg;
  ulong          msg_max;
  ulong          head;
  ulong          cnt;
};
typedef struct ag_sim_msg_queue ag_sim_msg_queue_t;

struct ag_sim_node {
  ag_pool_t *       pool;
  ag_votor_t *      votor;
  ag_epoch_info_t * epoch_info;
  ag_bls_sec_t      voting_key;
  long              now;

  ag_sim_msg_queue_t outbound;
  ag_sim_node_stats_t stats;
};
typedef struct ag_sim_node ag_sim_node_t;

struct ag_sim_delivery {
  long         at;
  ulong        seq;
  ushort       src;
  ushort       dst;
  ag_sim_msg_t msg;
};
typedef struct ag_sim_delivery ag_sim_delivery_t;

struct ag_sim_input {
  long            at;
  ulong           seq;
  ulong           node_mask;
  int             kind;
  ulong           slot;
  ag_block_info_t block;
};
typedef struct ag_sim_input ag_sim_input_t;

struct ag_sim {
  ag_sim_cfg_t cfg;
  long         now;

  ag_sim_node_t * node;
  long            link_delay[ AG_SIM_VALIDATOR_MAX ][ AG_SIM_VALIDATOR_MAX ];

  ag_sim_delivery_t * delivery_heap;
  ulong               delivery_cnt;
  ulong               delivery_seq;

  ag_sim_input_t * input_heap;
  ulong            input_cnt;
  ulong            input_seq;

  ag_sim_stats_t stats;
};

FD_FN_CONST char const *
ag_sim_strerror( int err ) {
  switch( err ) {
  case AG_SIM_SUCCESS:      return "success";
  case AG_SIM_ERR_INVAL:    return "invalid simulator argument";
  case AG_SIM_ERR_CAPACITY: return "simulator event capacity exceeded";
  case AG_SIM_ERR_POOL:     return "pool rejected a non-duplicate live message";
  case AG_SIM_ERR_BUDGET:   return "fixed-point transition budget exceeded";
  case AG_SIM_ERR_TIME:     return "invalid virtual time transition";
  default:                  return "unknown simulator error";
  }
}

ag_sim_cfg_t
ag_sim_cfg_default( void ) {
  return (ag_sim_cfg_t){
    .validator_cnt   = 5UL,
    .slot_max        = 32UL,
    .event_max       = 0UL,
    .transition_max  = 0UL,
    .seed            = 42UL,
    .shred_version   = (ushort)0x5a5a,
    .start_time_ns   = 0L,
    .network_delay_ns = 1000000L,
    .stakes          = NULL,
  };
}

static void *
sim_aligned_alloc( ulong align,
                   ulong sz ) {
  return aligned_alloc( align, fd_ulong_align_up( sz, align ) );
}

static int
msg_queue_push( ag_sim_msg_queue_t * queue,
                ag_sim_msg_t const * msg ) {
  if( FD_UNLIKELY( queue->cnt==queue->msg_max ) ) return 0;
  queue->msg[ (queue->head+queue->cnt) % queue->msg_max ] = *msg;
  queue->cnt++;
  return 1;
}

static ag_sim_msg_t
msg_queue_pop( ag_sim_msg_queue_t * queue ) {
  FD_TEST( queue->cnt );
  ag_sim_msg_t msg = queue->msg[ queue->head ];
  queue->head = (queue->head+1UL) % queue->msg_max;
  queue->cnt--;
  return msg;
}

FD_FN_PURE static int
delivery_before( ag_sim_delivery_t const * a,
                 ag_sim_delivery_t const * b ) {
  return a->at<b->at || (a->at==b->at && a->seq<b->seq);
}

static int
delivery_heap_push( ag_sim_t *                sim,
                    ag_sim_delivery_t const * delivery ) {
  if( FD_UNLIKELY( sim->delivery_cnt==sim->cfg.event_max ) ) return 0;
  ulong idx = sim->delivery_cnt++;
  while( idx ) {
    ulong parent = (idx-1UL) >> 1;
    if( FD_LIKELY( !delivery_before( delivery, &sim->delivery_heap[parent] ) ) ) break;
    sim->delivery_heap[idx] = sim->delivery_heap[parent];
    idx = parent;
  }
  sim->delivery_heap[idx] = *delivery;
  return 1;
}

static ag_sim_delivery_t
delivery_heap_pop( ag_sim_t * sim ) {
  FD_TEST( sim->delivery_cnt );
  ag_sim_delivery_t top  = sim->delivery_heap[0];
  ag_sim_delivery_t last = sim->delivery_heap[ --sim->delivery_cnt ];
  if( FD_UNLIKELY( !sim->delivery_cnt ) ) return top;

  ulong idx = 0UL;
  for(;;) {
    ulong left = 2UL*idx+1UL;
    if( FD_UNLIKELY( left>=sim->delivery_cnt ) ) break;
    ulong right = left+1UL;
    ulong child = (right<sim->delivery_cnt && delivery_before( &sim->delivery_heap[right], &sim->delivery_heap[left] )) ? right : left;
    if( FD_LIKELY( !delivery_before( &sim->delivery_heap[child], &last ) ) ) break;
    sim->delivery_heap[idx] = sim->delivery_heap[child];
    idx = child;
  }
  sim->delivery_heap[idx] = last;
  return top;
}

FD_FN_PURE static int
input_before( ag_sim_input_t const * a,
              ag_sim_input_t const * b ) {
  return a->at<b->at || (a->at==b->at && a->seq<b->seq);
}

static int
input_heap_push( ag_sim_t *             sim,
                 ag_sim_input_t const * input ) {
  if( FD_UNLIKELY( sim->input_cnt==sim->cfg.event_max ) ) return 0;
  ulong idx = sim->input_cnt++;
  while( idx ) {
    ulong parent = (idx-1UL) >> 1;
    if( FD_LIKELY( !input_before( input, &sim->input_heap[parent] ) ) ) break;
    sim->input_heap[idx] = sim->input_heap[parent];
    idx = parent;
  }
  sim->input_heap[idx] = *input;
  return 1;
}

static ag_sim_input_t
input_heap_pop( ag_sim_t * sim ) {
  FD_TEST( sim->input_cnt );
  ag_sim_input_t top  = sim->input_heap[0];
  ag_sim_input_t last = sim->input_heap[ --sim->input_cnt ];
  if( FD_UNLIKELY( !sim->input_cnt ) ) return top;

  ulong idx = 0UL;
  for(;;) {
    ulong left = 2UL*idx+1UL;
    if( FD_UNLIKELY( left>=sim->input_cnt ) ) break;
    ulong right = left+1UL;
    ulong child = (right<sim->input_cnt && input_before( &sim->input_heap[right], &sim->input_heap[left] )) ? right : left;
    if( FD_LIKELY( !input_before( &sim->input_heap[child], &last ) ) ) break;
    sim->input_heap[idx] = sim->input_heap[child];
    idx = child;
  }
  sim->input_heap[idx] = last;
  return top;
}

static int
take_transition( ag_sim_t * sim,
                 ulong *    budget ) {
  if( FD_UNLIKELY( !*budget ) ) return 0;
  (*budget)--;
  sim->stats.transition_cnt++;
  return 1;
}

static void
set_now( ag_sim_t * sim,
         long       now ) {
  sim->now = now;
  for( ulong i=0UL; i<sim->cfg.validator_cnt; i++ ) sim->node[i].now = now;
}

static int
cfg_prepare( ag_sim_cfg_t * cfg ) {
  if( FD_UNLIKELY( !cfg->validator_cnt || cfg->validator_cnt>AG_SIM_VALIDATOR_MAX ) ) return 0;
  if( FD_UNLIKELY( cfg->slot_max<AG_SLOTS_PER_WINDOW || cfg->slot_max>ULONG_MAX/(4UL*sizeof(ag_sim_msg_t)) ) ) return 0;
  if( FD_UNLIKELY( cfg->start_time_ns>AG_SIM_TIME_MAX ) ) return 0;
  if( FD_UNLIKELY( cfg->network_delay_ns<0L ) ) return 0;

  if( FD_UNLIKELY( !cfg->event_max ) ) {
    ulong scale = cfg->validator_cnt*cfg->validator_cnt;
    if( FD_UNLIKELY( scale>ULONG_MAX/cfg->slot_max ) ) return 0;
    scale *= cfg->slot_max;
    if( FD_UNLIKELY( scale>ULONG_MAX/8UL ) ) return 0;
    cfg->event_max = fd_ulong_max( 1024UL, 8UL*scale );
  }
  if( FD_UNLIKELY( cfg->event_max>ULONG_MAX/sizeof(ag_sim_delivery_t) ||
                   cfg->event_max>ULONG_MAX/sizeof(ag_sim_input_t) ) ) return 0;
  if( FD_UNLIKELY( !cfg->transition_max ) ) {
    if( FD_UNLIKELY( cfg->event_max>ULONG_MAX/64UL ) ) return 0;
    cfg->transition_max = 64UL*cfg->event_max;
  }
  return 1;
}

ag_sim_t *
ag_sim_new( ag_sim_cfg_t const * _cfg ) {
  if( FD_UNLIKELY( !_cfg ) ) return NULL;
  ag_sim_cfg_t cfg = *_cfg;
  if( FD_UNLIKELY( !cfg_prepare( &cfg ) ) ) return NULL;

  ulong total_stake = 0UL;
  for( ulong i=0UL; i<cfg.validator_cnt; i++ ) {
    ulong stake = cfg.stakes ? cfg.stakes[i] : 1UL;
    if( FD_UNLIKELY( stake>ULONG_MAX-total_stake ) ) return NULL;
    total_stake += stake;
  }
  if( FD_UNLIKELY( !total_stake ) ) return NULL;

  ag_sim_t * sim = (ag_sim_t *)calloc( 1UL, sizeof(ag_sim_t) );
  if( FD_UNLIKELY( !sim ) ) return NULL;
  sim->cfg        = cfg;
  sim->cfg.stakes = NULL; /* everything below owns a copy */
  sim->now        = cfg.start_time_ns;

  sim->node = (ag_sim_node_t *)calloc( cfg.validator_cnt, sizeof(ag_sim_node_t) );
  sim->delivery_heap = (ag_sim_delivery_t *)malloc( cfg.event_max*sizeof(ag_sim_delivery_t) );
  sim->input_heap    = (ag_sim_input_t *)malloc( cfg.event_max*sizeof(ag_sim_input_t) );
  if( FD_UNLIKELY( !sim->node || !sim->delivery_heap || !sim->input_heap ) ) {
    ag_sim_delete( sim );
    return NULL;
  }

  for( ulong src=0UL; src<cfg.validator_cnt; src++ ) {
    for( ulong dst=0UL; dst<cfg.validator_cnt; dst++ ) {
      sim->link_delay[src][dst] = src==dst ? 0L : cfg.network_delay_ns;
    }
  }

  ag_validator_info_t info[ AG_SIM_VALIDATOR_MAX ];
  fd_memset( info, 0, sizeof(info) );
  for( ulong i=0UL; i<cfg.validator_cnt; i++ ) {
    uchar ikm[ 32 ];
    for( ulong j=0UL; j<4UL; j++ ) {
      ulong word = fd_ulong_hash( cfg.seed ^ (0x9e3779b97f4a7c15UL*(i+1UL)) ^ (0xd6e8feb86659fd93UL*(j+1UL)) );
      FD_STORE( ulong, ikm+8UL*j, word );
      FD_STORE( ulong, info[i].id_key+8UL*j,   fd_ulong_hash( word ^ 0xa5a5a5a5a5a5a5a5UL ) );
      FD_STORE( ulong, info[i].vote_key+8UL*j, fd_ulong_hash( word ^ 0x5a5a5a5a5a5a5a5aUL ) );
    }
    ag_bls_sec_derive( sim->node[i].voting_key, ikm, sizeof(ikm) );

    info[i].id    = i;
    info[i].stake = cfg.stakes ? cfg.stakes[i] : 1UL;
    ag_bls_sec_to_pub( sim->node[i].voting_key, info[i].bls_key );
  }

  ulong outbound_max = 4UL*cfg.slot_max;
  for( ulong i=0UL; i<cfg.validator_cnt; i++ ) {
    ag_sim_node_t * node = &sim->node[i];
    node->now = cfg.start_time_ns;

    node->epoch_info = (ag_epoch_info_t *)sim_aligned_alloc( alignof(ag_epoch_info_t), sizeof(ag_epoch_info_t) );
    void * pool_mem  = sim_aligned_alloc( ag_pool_align(),  ag_pool_footprint ( cfg.slot_max ) );
    void * votor_mem = sim_aligned_alloc( ag_votor_align(), ag_votor_footprint( cfg.slot_max ) );
    node->outbound.msg = (ag_sim_msg_t *)malloc( outbound_max*sizeof(ag_sim_msg_t) );
    node->outbound.msg_max = outbound_max;
    if( FD_UNLIKELY( !node->epoch_info || !pool_mem || !votor_mem || !node->outbound.msg ) ) {
      free( pool_mem );
      free( votor_mem );
      ag_sim_delete( sim );
      return NULL;
    }

    fd_memset( node->epoch_info, 0, sizeof(ag_epoch_info_t) );
    ag_epoch_info( node->epoch_info, info, cfg.validator_cnt );
    node->pool = ag_pool_join( ag_pool_new( pool_mem, cfg.slot_max, fd_ulong_hash( cfg.seed ^ (2UL*i+0UL) ) ) );
    node->votor = ag_votor_join( ag_votor_new( votor_mem,
                                               cfg.slot_max,
                                               fd_ulong_hash( cfg.seed ^ (2UL*i+1UL) ) ) );
    if( FD_UNLIKELY( !node->pool || !node->votor ) ) {
      if( FD_UNLIKELY( !node->pool  ) ) free( pool_mem  );
      if( FD_UNLIKELY( !node->votor ) ) free( votor_mem );
      ag_sim_delete( sim );
      return NULL;
    }
    ag_pool_init               ( node->pool, 0UL );
    ag_pool_advance_epoch( node->pool, node->epoch_info, i, 0UL );
    ag_votor_init              ( node->votor, 0UL, cfg.start_time_ns );
    ag_votor_advance_epoch     ( node->votor, i, 0UL );
    ag_votor_set_bls_key       ( node->votor, node->voting_key );
    ag_votor_set_shred_version ( node->votor, cfg.shred_version );
  }

  return sim;
}

void
ag_sim_delete( ag_sim_t * sim ) {
  if( FD_UNLIKELY( !sim ) ) return;
  if( FD_LIKELY( sim->node ) ) {
    for( ulong i=0UL; i<sim->cfg.validator_cnt; i++ ) {
      ag_sim_node_t * node = &sim->node[i];
      if( node->pool  ) free( ag_pool_delete ( ag_pool_leave ( node->pool  ) ) );
      if( node->votor ) free( ag_votor_delete( ag_votor_leave( node->votor ) ) );
      free( node->epoch_info );
      free( node->outbound.msg );
    }
  }
  free( sim->node );
  free( sim->delivery_heap );
  free( sim->input_heap );
  free( sim );
}

int
ag_sim_set_link_delay( ag_sim_t * sim,
                       ulong      src,
                       ulong      dst,
                       long       delay_ns ) {
  if( FD_UNLIKELY( !sim || src>=sim->cfg.validator_cnt || dst>=sim->cfg.validator_cnt ) ) return AG_SIM_ERR_INVAL;
  if( FD_UNLIKELY( delay_ns<0L ) ) return AG_SIM_ERR_INVAL;
  sim->link_delay[src][dst] = delay_ns;
  return AG_SIM_SUCCESS;
}

ulong
ag_sim_all_nodes( ag_sim_t const * sim ) {
  return sim ? (1UL<<sim->cfg.validator_cnt)-1UL : 0UL;
}

static int
inject_input( ag_sim_t *             sim,
              long                   at_ns,
              ulong                  node_mask,
              int                    kind,
              ulong                  slot,
              ag_block_info_t const * block ) {
  if( FD_UNLIKELY( !sim || at_ns<sim->now || at_ns>AG_SIM_TIME_MAX || !slot ) ) return AG_SIM_ERR_INVAL;
  ulong all = ag_sim_all_nodes( sim );
  if( FD_UNLIKELY( !node_mask || (node_mask & ~all) ) ) return AG_SIM_ERR_INVAL;
  if( FD_UNLIKELY( kind==AG_SIM_INPUT_COMPLETED && (!block || block->parent.slot>=slot) ) ) return AG_SIM_ERR_INVAL;

  ag_sim_input_t input = { .at        = at_ns,
                           .seq       = sim->input_seq++,
                           .node_mask = node_mask,
                           .kind      = kind,
                           .slot      = slot };
  if( FD_LIKELY( block ) ) input.block = *block;
  return input_heap_push( sim, &input ) ? AG_SIM_SUCCESS : AG_SIM_ERR_CAPACITY;
}

int
ag_sim_inject_block( ag_sim_t *             sim,
                     long                   at_ns,
                     ulong                  node_mask,
                     ulong                  slot,
                     ag_block_info_t const * block ) {
  return inject_input( sim, at_ns, node_mask, AG_SIM_INPUT_COMPLETED, slot, block );
}

int
ag_sim_inject_dead( ag_sim_t * sim,
                    long       at_ns,
                    ulong      node_mask,
                    ulong      slot ) {
  return inject_input( sim, at_ns, node_mask, AG_SIM_INPUT_DEAD, slot, NULL );
}

static int
phase_inject( ag_sim_t * sim,
              ulong *    budget,
              int *      progressed ) {
  while( sim->input_cnt && sim->input_heap[0].at<=sim->now ) {
    if( FD_UNLIKELY( !take_transition( sim, budget ) ) ) return AG_SIM_ERR_BUDGET;
    ag_sim_input_t input = input_heap_pop( sim );
    *progressed = 1;

    for( ulong i=0UL; i<sim->cfg.validator_cnt; i++ ) {
      if( FD_UNLIKELY( !(input.node_mask & (1UL<<i)) ) ) continue;
      ag_sim_node_t * node = &sim->node[i];

      if( FD_LIKELY( input.kind==AG_SIM_INPUT_COMPLETED ) ) {
        ag_block_id_t block_id = ag_block_id( input.slot, input.block.hash );
        ag_pool_add_block( node->pool, &block_id, &input.block.parent );

        ag_event_block_t first_shred = { .seq  = input.seq,
                                         .ts   = sim->now,
                                         .kind = AG_EVENT_BLOCK_FIRST_SHRED,
                                         .slot = input.slot };
        ag_votor_handle_block_event( node->votor, &first_shred );

        ag_event_replay_t replay = { .seq        = input.seq,
                                     .ts         = sim->now,
                                     .kind       = AG_EVENT_REPLAY_COMPLETED,
                                     .slot       = input.slot,
                                     .block_info = input.block };
        ag_votor_handle_replay_event( node->votor, &replay );
        node->stats.completed_block_cnt++;
      } else {
        ag_event_replay_t replay = { .seq  = input.seq,
                                     .ts   = sim->now,
                                     .kind = AG_EVENT_REPLAY_DEAD,
                                     .slot = input.slot };
        ag_votor_handle_replay_event( node->votor, &replay );
        node->stats.dead_block_cnt++;
      }
    }
  }
  return AG_SIM_SUCCESS;
}

static int
phase_drain_votor( ag_sim_t * sim,
                   ulong *    budget,
                   int *      progressed ) {
  for( ulong i=0UL; i<sim->cfg.validator_cnt; i++ ) {
    ag_sim_node_t * node = &sim->node[i];
    ag_event_vote_t vote_event;
    ag_event_cert_t cert_event;
    int have_vote = ag_votor_poll_vote_event( node->votor, &vote_event );
    int have_cert = ag_votor_poll_cert_event( node->votor, &cert_event );

    while( have_vote || have_cert ) {
      if( FD_UNLIKELY( !take_transition( sim, budget ) ) ) return AG_SIM_ERR_BUDGET;
      ag_sim_msg_t msg = {0};
      if( have_vote && (!have_cert || vote_event.seq<cert_event.seq) ) {
        msg.kind       = AG_SIM_MSG_VOTE;
        msg.seq        = vote_event.seq;
        msg.ts         = vote_event.ts;
        msg.inner.vote = vote_event.vote;
        node->stats.vote_emit_cnt++;
        have_vote = ag_votor_poll_vote_event( node->votor, &vote_event );
      } else {
        msg.kind       = AG_SIM_MSG_CERT;
        msg.seq        = cert_event.seq;
        msg.ts         = cert_event.ts;
        msg.inner.cert = cert_event.cert;
        node->stats.cert_emit_cnt++;
        have_cert = ag_votor_poll_cert_event( node->votor, &cert_event );
      }
      if( FD_UNLIKELY( !msg_queue_push( &node->outbound, &msg ) ) ) return AG_SIM_ERR_CAPACITY;
      *progressed = 1;
    }
  }
  return AG_SIM_SUCCESS;
}

static int
phase_schedule_network( ag_sim_t * sim,
                        ulong *    budget,
                        int *      progressed ) {
  for( ulong src=0UL; src<sim->cfg.validator_cnt; src++ ) {
    ag_sim_msg_queue_t * outbound = &sim->node[src].outbound;
    while( outbound->cnt ) {
      if( FD_UNLIKELY( !take_transition( sim, budget ) ) ) return AG_SIM_ERR_BUDGET;
      ag_sim_msg_t msg = msg_queue_pop( outbound );
      *progressed = 1;

      for( ulong dst=0UL; dst<sim->cfg.validator_cnt; dst++ ) {
        long delay = sim->link_delay[src][dst];
        if( FD_UNLIKELY( delay==LONG_MAX ) ) {
          sim->stats.network_drop_cnt++;
          continue;
        }
        if( FD_UNLIKELY( delay>0L && sim->now>AG_SIM_TIME_MAX-delay ) ) return AG_SIM_ERR_TIME;

        ag_sim_delivery_t delivery = { .at  = sim->now+delay,
                                       .seq = sim->delivery_seq++,
                                       .src = (ushort)src,
                                       .dst = (ushort)dst,
                                       .msg = msg };
        if( FD_UNLIKELY( !delivery_heap_push( sim, &delivery ) ) ) return AG_SIM_ERR_CAPACITY;
      }
    }
  }
  return AG_SIM_SUCCESS;
}

static int
phase_deliver_network( ag_sim_t * sim,
                       ulong *    budget,
                       int *      progressed ) {
  while( sim->delivery_cnt && sim->delivery_heap[0].at<=sim->now ) {
    if( FD_UNLIKELY( !take_transition( sim, budget ) ) ) return AG_SIM_ERR_BUDGET;
    ag_sim_delivery_t delivery = delivery_heap_pop( sim );
    ag_sim_node_t *   node     = &sim->node[delivery.dst];
    int               pool_err;

    sim->stats.network_delivery_cnt++;
    *progressed = 1;
    if( FD_LIKELY( delivery.msg.kind==AG_SIM_MSG_VOTE ) ) {
      node->stats.vote_recv_cnt++;
      pool_err = ag_pool_add_vote( node->pool, &delivery.msg.inner.vote );
    } else {
      node->stats.cert_recv_cnt++;
      pool_err = ag_pool_add_cert( node->pool, &delivery.msg.inner.cert );
    }

    if( FD_LIKELY( pool_err==AG_POOL_SUCCESS ) ) continue;
    if( FD_LIKELY( pool_err==AG_POOL_ERR_DUPLICATE ) ) {
      node->stats.duplicate_msg_cnt++;
      continue;
    }
    if( FD_LIKELY( pool_err==AG_POOL_ERR_SLOT_OUT_OF_BOUNDS ) ) {
      node->stats.stale_msg_cnt++;
      continue;
    }
    return AG_SIM_ERR_POOL;
  }
  return AG_SIM_SUCCESS;
}

static int
phase_drain_pool( ag_sim_t * sim,
                  ulong *    budget,
                  int *      progressed ) {
  for( ulong i=0UL; i<sim->cfg.validator_cnt; i++ ) {
    ag_sim_node_t * node = &sim->node[i];
    ag_event_pool_t pool_event;
    while( ag_pool_poll_pool_event( node->pool, &pool_event ) ) {
      if( FD_UNLIKELY( !take_transition( sim, budget ) ) ) return AG_SIM_ERR_BUDGET;
      pool_event.ts = sim->now;
      ag_votor_handle_pool_event( node->votor, &pool_event, sim->now );
      node->stats.pool_event_cnt++;
      *progressed = 1;
    }

    /* Repair is outside the consensus feedback loop, but its queue must be
       drained so long simulations cannot fill it. */
    ag_event_repair_t repair_event;
    while( ag_pool_poll_repair_event( node->pool, &repair_event ) ) {
      if( FD_UNLIKELY( !take_transition( sim, budget ) ) ) return AG_SIM_ERR_BUDGET;
      node->stats.repair_event_cnt++;
      *progressed = 1;
    }
  }
  return AG_SIM_SUCCESS;
}

static int
phase_fire_timeouts( ag_sim_t * sim,
                     ulong *    budget,
                     int *      progressed ) {
  for( ulong i=0UL; i<sim->cfg.validator_cnt; i++ ) {
    ag_sim_node_t * node = &sim->node[i];
    ag_event_timeout_t timeout_event;
    while( ag_votor_poll_timeout_event( node->votor, sim->now, &timeout_event ) ) {
      if( FD_UNLIKELY( !take_transition( sim, budget ) ) ) return AG_SIM_ERR_BUDGET;
      ag_votor_handle_timeout_event( node->votor, &timeout_event );
      node->stats.timeout_event_cnt++;
      *progressed = 1;
    }
  }
  return AG_SIM_SUCCESS;
}

static int
run_fixed_point( ag_sim_t * sim,
                 ulong *    budget ) {
  for(;;) {
    int progressed = 0;
    int err;
    err = phase_inject          ( sim, budget, &progressed ); if( FD_UNLIKELY( err ) ) return err;
    err = phase_drain_votor     ( sim, budget, &progressed ); if( FD_UNLIKELY( err ) ) return err;
    err = phase_schedule_network( sim, budget, &progressed ); if( FD_UNLIKELY( err ) ) return err;
    err = phase_deliver_network ( sim, budget, &progressed ); if( FD_UNLIKELY( err ) ) return err;
    err = phase_drain_pool      ( sim, budget, &progressed ); if( FD_UNLIKELY( err ) ) return err;
    err = phase_fire_timeouts   ( sim, budget, &progressed ); if( FD_UNLIKELY( err ) ) return err;
    if( FD_LIKELY( !progressed ) ) return AG_SIM_SUCCESS;
  }
}

static long
next_event_time( ag_sim_t const * sim ) {
  long next = LONG_MAX;
  if( sim->input_cnt    ) next = fd_long_min( next, sim->input_heap[0].at );
  if( sim->delivery_cnt ) next = fd_long_min( next, sim->delivery_heap[0].at );
  for( ulong i=0UL; i<sim->cfg.validator_cnt; i++ ) {
    next = fd_long_min( next, ag_votor_next_timeout( sim->node[i].votor ) );
  }
  return next;
}

int
ag_sim_run( ag_sim_t * sim ) {
  if( FD_UNLIKELY( !sim ) ) return AG_SIM_ERR_INVAL;
  ulong budget = sim->cfg.transition_max;
  return run_fixed_point( sim, &budget );
}

int
ag_sim_run_until( ag_sim_t * sim,
                  long       end_time_ns ) {
  if( FD_UNLIKELY( !sim ) ) return AG_SIM_ERR_INVAL;
  if( FD_UNLIKELY( end_time_ns<sim->now || end_time_ns>AG_SIM_TIME_MAX ) ) return AG_SIM_ERR_TIME;

  ulong budget = sim->cfg.transition_max;
  for(;;) {
    int err = run_fixed_point( sim, &budget );
    if( FD_UNLIKELY( err ) ) return err;
    if( FD_LIKELY( sim->now==end_time_ns ) ) return AG_SIM_SUCCESS;

    long next = next_event_time( sim );
    if( FD_UNLIKELY( next<=sim->now ) ) return AG_SIM_ERR_TIME;
    set_now( sim, fd_long_min( next, end_time_ns ) );
  }
}

ulong
ag_sim_validator_cnt( ag_sim_t const * sim ) {
  return sim ? sim->cfg.validator_cnt : 0UL;
}

long
ag_sim_now( ag_sim_t const * sim ) {
  return sim ? sim->now : LONG_MIN;
}

long
ag_sim_node_now( ag_sim_t const * sim,
                 ulong            node_idx ) {
  return sim && node_idx<sim->cfg.validator_cnt ? sim->node[node_idx].now : LONG_MIN;
}

ag_pool_t *
ag_sim_node_pool( ag_sim_t * sim,
                  ulong      node_idx ) {
  return sim && node_idx<sim->cfg.validator_cnt ? sim->node[node_idx].pool : NULL;
}

ag_votor_t *
ag_sim_node_votor( ag_sim_t * sim,
                   ulong      node_idx ) {
  return sim && node_idx<sim->cfg.validator_cnt ? sim->node[node_idx].votor : NULL;
}

ag_epoch_info_t const *
ag_sim_node_epoch_info( ag_sim_t const * sim,
                        ulong            node_idx ) {
  return sim && node_idx<sim->cfg.validator_cnt ? sim->node[node_idx].epoch_info : NULL;
}

ag_sim_node_stats_t const *
ag_sim_node_stats( ag_sim_t const * sim,
                   ulong            node_idx ) {
  return sim && node_idx<sim->cfg.validator_cnt ? &sim->node[node_idx].stats : NULL;
}

ag_sim_stats_t const *
ag_sim_stats( ag_sim_t const * sim ) {
  return sim ? &sim->stats : NULL;
}
