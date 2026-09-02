#ifndef HEADER_fd_src_choreo_votor_ag_sim_h
#define HEADER_fd_src_choreo_votor_ag_sim_h

/* ag_sim is a deterministic, single-process Alpenglow consensus simulator.
   It is a hosted test utility: every logical validator owns an independent
   ag_pool and ag_votor, while votes and certificates travel over a virtual
   all-to-all network.

   Work at a given timestamp is processed to a fixed point in this order:

     1. completed/dead replay events
     2. Votor vote/certificate output
     3. outbound queue scheduling
     4. due network deliveries into Pool
     5. Pool events into Votor
     6. due Votor timeouts

   Node index and insertion sequence break all remaining ties. */

#include "ag_pool.h"
#include "ag_votor.h"

#define AG_SIM_VALIDATOR_MAX (20UL)

#define AG_SIM_SUCCESS       ( 0)
#define AG_SIM_ERR_INVAL     (-1)
#define AG_SIM_ERR_CAPACITY  (-2)
#define AG_SIM_ERR_POOL      (-3)
#define AG_SIM_ERR_BUDGET    (-4)
#define AG_SIM_ERR_TIME      (-5)

struct ag_sim_cfg {
  ulong         validator_cnt;   /* [1, AG_SIM_VALIDATOR_MAX] */
  ulong         slot_max;        /* at least AG_SLOTS_PER_WINDOW */
  ulong         event_max;       /* 0 selects a size from validator_cnt/slot_max */
  ulong         transition_max;  /* per run call; 0 selects a conservative default */
  ulong         seed;
  ushort        shred_version;
  long          start_time_ns;
  long          network_delay_ns;
  ulong const * stakes;          /* validator_cnt entries, NULL means equal stake */
};
typedef struct ag_sim_cfg ag_sim_cfg_t;

struct ag_sim_node_stats {
  ulong completed_block_cnt;
  ulong dead_block_cnt;
  ulong vote_emit_cnt;
  ulong cert_emit_cnt;
  ulong vote_recv_cnt;
  ulong cert_recv_cnt;
  ulong duplicate_msg_cnt;
  ulong stale_msg_cnt;
  ulong pool_event_cnt;
  ulong repair_event_cnt;
  ulong timeout_event_cnt;
};
typedef struct ag_sim_node_stats ag_sim_node_stats_t;

struct ag_sim_stats {
  ulong transition_cnt;
  ulong network_delivery_cnt;
  ulong network_drop_cnt;
};
typedef struct ag_sim_stats ag_sim_stats_t;

typedef struct ag_sim ag_sim_t;

FD_PROTOTYPES_BEGIN

FD_FN_CONST char const *
ag_sim_strerror( int err );

ag_sim_cfg_t
ag_sim_cfg_default( void );

/* ag_sim_new copies cfg and stakes.  All nodes begin at cfg.start_time_ns
   with a finalized zero-hash genesis block. */

ag_sim_t *
ag_sim_new( ag_sim_cfg_t const * cfg );

void
ag_sim_delete( ag_sim_t * sim );

/* A link delay of LONG_MAX disables the directed link.  Reconfiguring a link
   does not affect messages which have already been scheduled. */

int
ag_sim_set_link_delay( ag_sim_t * sim,
                       ulong      src,
                       ulong      dst,
                       long       delay_ns );

FD_FN_PURE ulong
ag_sim_all_nodes( ag_sim_t const * sim );

/* Schedule replay input for the selected nodes.  A completed block also
   injects FIRST_SHRED and registers the block/parent relation in Pool. */

int
ag_sim_inject_block( ag_sim_t *             sim,
                     long                   at_ns,
                     ulong                  node_mask,
                     ulong                  slot,
                     ag_block_info_t const * block );

int
ag_sim_inject_dead( ag_sim_t * sim,
                    long       at_ns,
                    ulong      node_mask,
                    ulong      slot );

/* ag_sim_run drains only work due at the current virtual time.
   ag_sim_run_until advances to every intervening network, replay, or timeout
   deadline, reaching a fixed point at each timestamp and at end_time_ns. */

int
ag_sim_run( ag_sim_t * sim );

int
ag_sim_run_until( ag_sim_t * sim,
                  long       end_time_ns );

FD_FN_PURE ulong
ag_sim_validator_cnt( ag_sim_t const * sim );

FD_FN_PURE long
ag_sim_now( ag_sim_t const * sim );

FD_FN_PURE long
ag_sim_node_now( ag_sim_t const * sim,
                 ulong            node_idx );

ag_pool_t *
ag_sim_node_pool( ag_sim_t * sim,
                  ulong      node_idx );

ag_votor_t *
ag_sim_node_votor( ag_sim_t * sim,
                   ulong      node_idx );

ag_epoch_info_t const *
ag_sim_node_epoch_info( ag_sim_t const * sim,
                        ulong            node_idx );

ag_sim_node_stats_t const *
ag_sim_node_stats( ag_sim_t const * sim,
                   ulong            node_idx );

ag_sim_stats_t const *
ag_sim_stats( ag_sim_t const * sim );

FD_PROTOTYPES_END

#endif /* HEADER_fd_src_choreo_votor_ag_sim_h */
