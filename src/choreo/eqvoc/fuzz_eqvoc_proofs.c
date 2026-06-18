#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include <stdlib.h>
#include <string.h>

#include "fd_eqvoc.h"
#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"

#define FUZZ_DUP_MAX     8UL
#define FUZZ_FEC_MAX     8UL
#define FUZZ_PER_VTR_MAX 8UL
#define FUZZ_VTR_MAX     4UL
#define FUZZ_ROOT        0UL
#define FUZZ_VERSION     42U
#define FUZZ_RECIPE_MIN  64UL

enum {
  MODE_DD_LAST = 0,
  MODE_DD_SAME_FEC,
  MODE_DC_SAME_FEC,
  MODE_CD_SAME_FEC,
  MODE_CC_SAME_FEC,
  MODE_DD_IGNORED,
  MODE_TRUNC_SHRED1,
  MODE_TRUNC_SHRED2,
  MODE_SLOT_MISMATCH,
  MODE_VERSION_MISMATCH,
  MODE_TYPE_UNCHAINED,
  MODE_MERKLE_DEPTH,
  MODE_BAD_CHUNK_LEN,
  MODE_BAD_CHUNK_CNT,
  MODE_BAD_CHUNK_IDX,
  MODE_BAD_FROM,
  MODE_OLD_SLOT,
  MODE_SIGCHECK,
  MODE_CNT
};

typedef struct {
  uchar const * data;
  ulong         data_sz;
  ulong         off;
  ulong         salt;
} fuzz_reader_t;

static fd_pubkey_t        voters[ 2 ];
static uint               sched[ 128 ];
static fd_epoch_leaders_t leaders = { .slot0 = 1UL, .slot_cnt = 128UL, .pub = voters, .pub_cnt = 1UL, .sched = sched, .sched_cnt = 128UL };
static fd_gossip_duplicate_shred_t chunks_out[ FD_EQVOC_CHUNK_CNT ];
static uchar *            fuzz_eqvoc_mem;
static ulong              fuzz_eqvoc_footprint;

static uchar
fuzz_u8( fuzz_reader_t * r ) {
  if( FD_LIKELY( r->off<r->data_sz ) ) return r->data[ r->off++ ];
  r->salt = 6364136223846793005UL*r->salt + 1442695040888963407UL;
  return (uchar)( r->salt>>56 );
}

static ulong
fuzz_range( fuzz_reader_t * r,
            ulong           n ) {
  if( FD_UNLIKELY( n<=1UL ) ) return 0UL;
  ulong x = 0UL;
  for( ulong shift=0UL, lim=n-1UL; lim; shift+=8UL, lim>>=8UL )
    x |= (ulong)fuzz_u8( r ) << shift;
  return x % n;
}

static ulong
fuzz_ulong( fuzz_reader_t * r ) {
  ulong x = 0UL;
  for( ulong i=0UL; i<sizeof(ulong); i++ ) x |= (ulong)fuzz_u8( r ) << (8UL*i);
  return x;
}

static void
fuzz_bytes( fuzz_reader_t * r,
            uchar *         dst,
            ulong           sz ) {
  for( ulong i=0UL; i<sz; i++ ) dst[ i ] = fuzz_u8( r );
}

static void
init_voters( void ) {
  for( ulong i=0UL; i<sizeof(voters); i++ ) ((uchar *)voters)[ i ] = (uchar)( 0x31U + 17U*i );
  for( ulong i=0UL; i<128UL; i++ ) sched[ i ] = 0U;
}

static void
fuzz_cleanup( void ) {
  free( fuzz_eqvoc_mem );
  fuzz_eqvoc_mem = NULL;
  fd_halt();
}

static void
make_shred( uchar *         buf,
            int             is_code,
            ulong           slot,
            ushort          version,
            uint            fec_set_idx,
            uint            idx,
            uchar           flags,
            uchar           variant_type,
            uchar           merkle_cnt,
            fuzz_reader_t * r ) {
  ulong sz = is_code ? FD_SHRED_MAX_SZ : FD_SHRED_MIN_SZ;
  memset( buf, 0, sz );

  fd_shred_t * shred = (fd_shred_t *)fd_type_pun( buf );

  fuzz_bytes( r, shred->signature, FD_SHRED_SIGNATURE_SZ );
  shred->variant     = fd_shred_variant( variant_type, merkle_cnt );
  shred->slot        = slot;
  shred->idx         = idx;
  shred->version     = version;
  shred->fec_set_idx = fec_set_idx;

  if( is_code ) {
    shred->code.data_cnt = 8U;
    shred->code.code_cnt = 8U;
    shred->code.idx      = (ushort)( idx - fec_set_idx - shred->code.data_cnt );
  } else {
    shred->data.parent_off = (ushort)( slot ? 1U : 0U );
    shred->data.flags      = flags;
    shred->data.size       = (ushort)( FD_SHRED_DATA_HEADER_SZ + 900UL + fuzz_range( r, 32UL ) );
  }

  uchar * payload = buf + (is_code ? FD_SHRED_CODE_HEADER_SZ : FD_SHRED_DATA_HEADER_SZ);
  fuzz_bytes( r, payload, 256UL );

  if( fd_shred_is_chained( variant_type ) ) {
    uchar * chain = buf + fd_shred_chain_off( shred->variant );
    fuzz_bytes( r, chain, FD_SHRED_MERKLE_ROOT_SZ );
  }

  ulong merkle_off = fd_shred_merkle_off( shred );
  ulong merkle_sz  = fd_shred_merkle_sz( shred->variant );
  fuzz_bytes( r, buf + merkle_off, merkle_sz );
}

static ulong
proof_chunk2_len( int is_code1,
                  int is_code2 ) {
  if( is_code1 & is_code2 ) return FD_EQVOC_CHUNK2_LEN_CC;
  if( (!is_code1) & (!is_code2) ) return FD_EQVOC_CHUNK2_LEN_DD;
  return FD_EQVOC_CHUNK2_LEN_DC;
}

static void
build_chunks( fd_gossip_duplicate_shred_t chunks[ static FD_EQVOC_CHUNK_CNT ],
              uchar const *               shred1,
              ulong                       shred1_sz,
              uchar const *               shred2,
              ulong                       shred2_sz,
              ulong                       enc_shred1_sz,
              ulong                       enc_shred2_sz,
              ulong                       slot,
              int                         is_code1,
              int                         is_code2 ) {
  uchar proof[ 2UL*sizeof(ulong) + 2UL*FD_SHRED_MAX_SZ ];
  uchar * p = proof;

  FD_STORE( ulong, p, enc_shred1_sz );
  p += sizeof(ulong);
  memcpy( p, shred1, shred1_sz );
  p += shred1_sz;
  FD_STORE( ulong, p, enc_shred2_sz );
  p += sizeof(ulong);
  memcpy( p, shred2, shred2_sz );

  for( uchar i=0U; i<FD_EQVOC_CHUNK_CNT; i++ ) {
    memset( &chunks[ i ], 0, sizeof(chunks[ i ]) );
    chunks[ i ].index       = (ushort)i;
    chunks[ i ].slot        = slot;
    chunks[ i ].num_chunks  = FD_EQVOC_CHUNK_CNT;
    chunks[ i ].chunk_index = i;
  }

  chunks[ 0 ].chunk_len = FD_EQVOC_CHUNK0_LEN;
  chunks[ 1 ].chunk_len = FD_EQVOC_CHUNK1_LEN;
  chunks[ 2 ].chunk_len = proof_chunk2_len( is_code1, is_code2 );

  memcpy( chunks[ 0 ].chunk, proof,                         chunks[ 0 ].chunk_len );
  memcpy( chunks[ 1 ].chunk, proof + FD_EQVOC_CHUNK_SZ,      chunks[ 1 ].chunk_len );
  memcpy( chunks[ 2 ].chunk, proof + 2UL*FD_EQVOC_CHUNK_SZ,  chunks[ 2 ].chunk_len );
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
  init_voters();

  fuzz_eqvoc_footprint = fd_eqvoc_footprint( FUZZ_DUP_MAX, FUZZ_FEC_MAX, FUZZ_PER_VTR_MAX, FUZZ_VTR_MAX );
  fuzz_eqvoc_footprint = FD_ULONG_ALIGN_UP( fuzz_eqvoc_footprint, fd_eqvoc_align() );
  fuzz_eqvoc_mem = aligned_alloc( fd_eqvoc_align(), fuzz_eqvoc_footprint );
  if( FD_UNLIKELY( !fuzz_eqvoc_mem ) ) abort();

  atexit( fuzz_cleanup );
  return 0;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {
  fuzz_reader_t r = { .data = data, .data_sz = size, .off = 0UL, .salt = size ^ 0x9e3779b97f4a7c15UL };

  int   mode    = (int)fuzz_range( &r, MODE_CNT );
  ulong slot    = 1UL + fuzz_range( &r, 96UL );
  ushort version = (ushort)( FUZZ_VERSION + fuzz_range( &r, 3UL ) );

  int is_code1 = 0;
  int is_code2 = 0;
  int same_fec = 1;
  int last_conflict = 0;

  switch( mode ) {
  case MODE_DC_SAME_FEC: is_code2 = 1; break;
  case MODE_CD_SAME_FEC: is_code1 = 1; break;
  case MODE_CC_SAME_FEC: is_code1 = 1; is_code2 = 1; break;
  case MODE_DD_LAST:     same_fec = 0; last_conflict = 1; break;
  case MODE_DD_IGNORED:  same_fec = 0; break;
  case MODE_SIGCHECK:    is_code1 = !!(fuzz_u8( &r ) & 1U); is_code2 = !!(fuzz_u8( &r ) & 1U); break;
  default: break;
  }

  uchar shred1[ FD_SHRED_MAX_SZ ];
  uchar shred2[ FD_SHRED_MAX_SZ ];

  uint fec1 = 4U + (uint)fuzz_range( &r, 4UL );
  uint fec2 = same_fec ? fec1 : fec1 + 1U;
  uint idx1 = is_code1 ? fec1 + 8U + (uint)fuzz_range( &r, 4UL ) : fec1;
  uint idx2 = is_code2 ? fec2 + 8U + (uint)fuzz_range( &r, 4UL ) : fec2;

  if( last_conflict ) {
    idx1 = fec1;
    idx2 = fec2 + 1U;
  }

  uchar type1 = is_code1 ? FD_SHRED_TYPE_MERKLE_CODE_CHAINED : FD_SHRED_TYPE_MERKLE_DATA_CHAINED;
  uchar type2 = is_code2 ? FD_SHRED_TYPE_MERKLE_CODE_CHAINED : FD_SHRED_TYPE_MERKLE_DATA_CHAINED;
  if( fuzz_u8( &r ) & 1U ) type1 = is_code1 ? FD_SHRED_TYPE_MERKLE_CODE_CHAINED_RESIGNED : FD_SHRED_TYPE_MERKLE_DATA_CHAINED_RESIGNED;
  if( fuzz_u8( &r ) & 1U ) type2 = is_code2 ? FD_SHRED_TYPE_MERKLE_CODE_CHAINED_RESIGNED : FD_SHRED_TYPE_MERKLE_DATA_CHAINED_RESIGNED;
  uchar merkle_cnt1 = FD_SHRED_MERKLE_LAYER_CNT - 1U;
  uchar merkle_cnt2 = FD_SHRED_MERKLE_LAYER_CNT - 1U;
  if( mode==MODE_TYPE_UNCHAINED ) type1 = is_code1 ? FD_SHRED_TYPE_MERKLE_CODE : FD_SHRED_TYPE_MERKLE_DATA;
  if( mode==MODE_MERKLE_DEPTH  ) merkle_cnt1 = FD_SHRED_MERKLE_LAYER_CNT - 2U;

  uchar flags1 = (uchar)( fuzz_u8( &r ) & FD_SHRED_DATA_REF_TICK_MASK );
  uchar flags2 = (uchar)( fuzz_u8( &r ) & FD_SHRED_DATA_REF_TICK_MASK );
  if( last_conflict ) flags1 |= FD_SHRED_DATA_FLAG_SLOT_COMPLETE | FD_SHRED_DATA_FLAG_DATA_COMPLETE;

  make_shred( shred1, is_code1, slot, version, fec1, idx1, flags1, type1, merkle_cnt1, &r );
  make_shred( shred2, is_code2, slot, version, fec2, idx2, flags2, type2, merkle_cnt2, &r );

  ulong shred1_sz = is_code1 ? FD_SHRED_MAX_SZ : FD_SHRED_MIN_SZ;
  ulong shred2_sz = is_code2 ? FD_SHRED_MAX_SZ : FD_SHRED_MIN_SZ;
  ulong enc_shred1_sz = shred1_sz;
  ulong enc_shred2_sz = shred2_sz;

  if( mode==MODE_TRUNC_SHRED1 ) enc_shred1_sz++;
  if( mode==MODE_TRUNC_SHRED2 ) enc_shred2_sz++;

  if( mode==MODE_SLOT_MISMATCH ) {
    fd_shred_t * s2 = (fd_shred_t *)fd_type_pun( shred2 );
    s2->slot = slot + 1UL;
  }
  if( mode==MODE_VERSION_MISMATCH ) {
    fd_shred_t * s2 = (fd_shred_t *)fd_type_pun( shred2 );
    s2->version = (ushort)( version + 1U );
  }

  fd_gossip_duplicate_shred_t chunks[ FD_EQVOC_CHUNK_CNT ];
  build_chunks( chunks, shred1, shred1_sz, shred2, shred2_sz,
                enc_shred1_sz, enc_shred2_sz, slot, is_code1, is_code2 );

  if( mode==MODE_BAD_CHUNK_LEN ) chunks[ fuzz_range( &r, FD_EQVOC_CHUNK_CNT ) ].chunk_len ^= 1UL + fuzz_range( &r, 7UL );
  if( mode==MODE_BAD_CHUNK_CNT ) chunks[ fuzz_range( &r, FD_EQVOC_CHUNK_CNT ) ].num_chunks = (uchar)( FD_EQVOC_CHUNK_CNT + 1UL + fuzz_range( &r, 4UL ) );
  if( mode==MODE_BAD_CHUNK_IDX ) chunks[ fuzz_range( &r, FD_EQVOC_CHUNK_CNT ) ].chunk_index = (uchar)( FD_EQVOC_CHUNK_CNT + fuzz_range( &r, 4UL ) );
  if( mode==MODE_OLD_SLOT      ) for( ulong i=0UL; i<FD_EQVOC_CHUNK_CNT; i++ ) chunks[ i ].slot = FUZZ_ROOT;

  fd_eqvoc_t * eqvoc = fd_eqvoc_join( fd_eqvoc_new( fuzz_eqvoc_mem, FUZZ_DUP_MAX, FUZZ_FEC_MAX, FUZZ_PER_VTR_MAX, FUZZ_VTR_MAX, fuzz_ulong( &r ) ) );
  fd_eqvoc_update_voters( eqvoc, voters, 2UL );

  fd_pubkey_t const * from = ( mode==MODE_BAD_FROM ) ? &((fd_pubkey_t const){ .uc = { 0xffU } }) : &voters[ fuzz_range( &r, 2UL ) ];
  fd_epoch_leaders_t const * opt_leaders = ( mode==MODE_SIGCHECK ) ? &leaders : NULL;

  static uchar const order_tbl[ 6 ][ 3 ] = {
    { 0U, 1U, 2U }, { 0U, 2U, 1U }, { 1U, 0U, 2U },
    { 1U, 2U, 0U }, { 2U, 0U, 1U }, { 2U, 1U, 0U }
  };
  uchar const * order = order_tbl[ fuzz_range( &r, 6UL ) ];

  int last_err = FD_EQVOC_IGNORED;
  for( ulong i=0UL; i<FD_EQVOC_CHUNK_CNT; i++ ) {
    last_err = fd_eqvoc_chunk_insert( eqvoc, FUZZ_ROOT, version, opt_leaders, from, &chunks[ order[ i ] ], chunks_out );
    switch( last_err ) {
    case FD_EQVOC_SUCCESS:        FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_IGNORED:        FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_SERDE:      FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_SLOT:       FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_VERSION:    FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_TYPE:       FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_MERKLE:     FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_SIG:        FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_CHUNK_CNT:  FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_CHUNK_IDX:  FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_CHUNK_LEN:  FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_CHUNK_FROM: FD_FUZZ_MUST_BE_COVERED; break;
    case FD_EQVOC_ERR_CHUNK_SLOT: FD_FUZZ_MUST_BE_COVERED; break;
    default: abort();
    }
    if( FD_UNLIKELY( last_err!=FD_EQVOC_IGNORED ) ) break;
  }

  if( FD_UNLIKELY( last_err==FD_EQVOC_SUCCESS ) ) {
    FD_FUZZ_MUST_BE_COVERED;
    int dup_err = fd_eqvoc_chunk_insert( eqvoc, FUZZ_ROOT, version, opt_leaders, from, &chunks[ 0 ], chunks_out );
    if( dup_err==FD_EQVOC_IGNORED ) FD_FUZZ_MUST_BE_COVERED;
  } else if( mode==MODE_DD_IGNORED && last_err==FD_EQVOC_IGNORED ) {
    FD_FUZZ_MUST_BE_COVERED;
  }

  fd_eqvoc_delete( fd_eqvoc_leave( eqvoc ) );
  return 0;
}

ulong
LLVMFuzzerCustomMutator( uchar * data,
                         ulong   size,
                         ulong   max_size,
                         uint    seed ) {
  (void)seed;
  if( FD_UNLIKELY( max_size<FUZZ_RECIPE_MIN ) ) return 0UL;
  if( size<FUZZ_RECIPE_MIN ) {
    memset( data + size, 0, FUZZ_RECIPE_MIN - size );
    size = FUZZ_RECIPE_MIN;
  }

  size = LLVMFuzzerMutate( data, size, max_size );

  if( size<FUZZ_RECIPE_MIN ) {
    memset( data + size, 0, FUZZ_RECIPE_MIN - size );
    size = FUZZ_RECIPE_MIN;
  }
  data[ 0 ] = (uchar)( data[ 0 ] % MODE_CNT );
  return size;
}
