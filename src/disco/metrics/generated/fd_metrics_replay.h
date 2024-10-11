/* THIS FILE IS GENERATED BY gen_metrics.py. DO NOT HAND EDIT. */

#include "../fd_metrics_base.h"

#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_OFF  (176UL)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_CNT  (4UL)

#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_SNAPSHOT_BEGIN_OFF  (176UL)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_SNAPSHOT_BEGIN_NAME "replay_snapshot_status_snapshot_begin"
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_SNAPSHOT_BEGIN_TYPE (FD_METRICS_TYPE_COUNTER)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_SNAPSHOT_BEGIN_DESC "The snapshot and incremental snapshot progress (Set immediately before the call to fd_snapshot_load)"

#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_SNAPSHOT_END_OFF  (177UL)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_SNAPSHOT_END_NAME "replay_snapshot_status_snapshot_end"
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_SNAPSHOT_END_TYPE (FD_METRICS_TYPE_COUNTER)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_SNAPSHOT_END_DESC "The snapshot and incremental snapshot progress (Set after fd_snapshot_load has completed)"

#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_INCREMENTAL_BEGIN_OFF  (178UL)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_INCREMENTAL_BEGIN_NAME "replay_snapshot_status_incremental_begin"
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_INCREMENTAL_BEGIN_TYPE (FD_METRICS_TYPE_COUNTER)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_INCREMENTAL_BEGIN_DESC "The snapshot and incremental snapshot progress (Set immediately before the call to fd_snapshot_load)"

#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_INCREMENTAL_END_OFF  (179UL)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_INCREMENTAL_END_NAME "replay_snapshot_status_incremental_end"
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_INCREMENTAL_END_TYPE (FD_METRICS_TYPE_COUNTER)
#define FD_METRICS_COUNTER_REPLAY_SNAPSHOT_STATUS_INCREMENTAL_END_DESC "The snapshot and incremental snapshot progress (Set after fd_snapshot_load has completed)"


#define FD_METRICS_REPLAY_TOTAL (4UL)
extern const fd_metrics_meta_t FD_METRICS_REPLAY[FD_METRICS_REPLAY_TOTAL];
