ifdef FD_HAS_INT128
$(call add-hdrs,fd_acc_mgr.h)
$(call add-objs,fd_acc_mgr,fd_flamenco)

$(call add-hdrs,fd_account.h)
$(call add-objs,fd_account,fd_flamenco)

$(call add-hdrs,fd_bank_hash_cmp.h fd_rwseq_lock.h)
$(call add-objs,fd_bank_hash_cmp,fd_flamenco)

$(call add-hdrs,fd_blockstore.h fd_rwseq_lock.h)
$(call add-objs,fd_blockstore,fd_flamenco)

$(call add-hdrs,fd_borrowed_account.h)
$(call add-objs,fd_borrowed_account,fd_flamenco)

$(call add-hdrs,fd_executor.h)
$(call add-objs,fd_executor,fd_flamenco)

$(call add-hdrs,fd_hashes.h)
$(call add-objs,fd_hashes,fd_flamenco)

$(call add-hdrs,fd_pubkey_utils.h)
$(call add-objs,fd_pubkey_utils,fd_flamenco)

$(call add-hdrs,fd_rent_lists.h)

ifdef FD_HAS_ATOMIC
$(call add-hdrs,fd_runtime.h fd_runtime_init.h fd_runtime_err.h)
$(call add-objs,fd_runtime fd_runtime_init,fd_flamenco)
endif
endif

$(call add-hdrs,fd_system_ids.h)
$(call add-objs,fd_system_ids,fd_flamenco)
$(call make-unit-test,test_system_ids,test_system_ids,fd_flamenco fd_util fd_ballet)
$(call run-unit-test,test_system_ids,)

ifdef FD_HAS_ROCKSDB
$(call add-hdrs,fd_rocksdb.h)
$(call add-objs,fd_rocksdb,fd_flamenco)
endif

ifdef FD_HAS_ATOMIC
$(call add-hdrs,fd_txncache.h)
$(call add-objs,fd_txncache,fd_flamenco)
ifdef FD_HAS_HOSTED
$(call make-unit-test,test_txncache,test_txncache,fd_flamenco fd_util)
$(call run-unit-test,test_txncache,)
endif
endif
