#if !FD_HAS_HOSTED
#error "This target requires FD_HAS_HOSTED"
#endif

#include <stdlib.h>
#include <string.h>

#include "../../util/fd_util.h"
#include "../../util/sanitize/fd_fuzz.h"
#include "../hfork/fd_hfork.h"
#include "fd_votes.h"

/* This is an actor/program fuzzer for the fork-aware vote transaction
   structures.  It intentionally stays small: all inputs are decoded
   into bounded operations over synthetic voters, slots, block IDs, and
   bank hashes before touching fd_votes_t or fd_hfork_t. */

#define FUZZ_VTR_MAX     (8UL)
#define FUZZ_SLOT_MAX    (16UL)
#define FUZZ_PER_VTR_MAX (8UL)
#define FUZZ_BLOCK_MAX   (24UL)
#define FUZZ_BANK_MAX    (8UL)
#define FUZZ_ACTION_MAX  (96UL)
#define FUZZ_ROOT_BASE   (1000UL)

typedef struct {
  uchar const * data;
  ulong         data_sz;
  ulong         off;
  ulong         salt;
} fuzz_reader_t;

typedef struct {
  ulong block_idx;
  ulong bank_idx;
  ulong slot;
  ulong stake;
} hfork_vote_t;

typedef struct {
  fd_pubkey_t  pubkey;
  ulong        stake;
  int          active;
  ulong        bit;
  hfork_vote_t hfork_vote[ FUZZ_PER_VTR_MAX ];
  ulong        hfork_vote_cnt;
} voter_model_t;

typedef struct {
  ulong block_idx;
  ulong stake;
  uchar flags;
} votes_blk_model_t;

typedef struct {
  int               present;
  ulong             slot;
  ulong             bits;
  votes_blk_model_t blk[ FUZZ_VTR_MAX ];
  ulong             blk_cnt;
} votes_slot_model_t;

typedef struct {
  int   present;
  ulong block_idx;
  ulong bank_idx;
  ulong stake;
  ulong order;
} hfork_pair_model_t;

typedef struct {
  int   known;
  int   dead;
  ulong bank_idx;
} our_bank_model_t;

typedef struct {
  voter_model_t      voter[ FUZZ_VTR_MAX ];
  votes_slot_model_t votes_slot[ FUZZ_SLOT_MAX ];
  hfork_pair_model_t hfork_pair[ FUZZ_PER_VTR_MAX * FUZZ_VTR_MAX ];
  our_bank_model_t   our_bank[ FUZZ_BLOCK_MAX ];
  ulong              root;
  ulong              order_seq;

  int   have_last_vote;
  ulong last_voter_idx;
  ulong last_slot;
  ulong last_block_idx;
  ulong last_bank_idx;
} fuzz_model_t;

static void *      fuzz_votes_mem;
static void *      fuzz_hfork_mem;
static fuzz_model_t fuzz_model[ 1 ];

static void
fuzz_cleanup( void ) {
  free( fuzz_votes_mem );
  free( fuzz_hfork_mem );
  fuzz_votes_mem = NULL;
  fuzz_hfork_mem = NULL;
  fd_halt();
}

static uchar
fuzz_u8( fuzz_reader_t * r ) {
  if( FD_LIKELY( r->off<r->data_sz ) ) return r->data[ r->off++ ];
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

static void
pubkey_from_idx( fd_pubkey_t * out,
                 ulong         idx ) {
  for( ulong i=0UL; i<4UL; i++ )
    out->ul[ i ] = 0xf17edace00000000UL ^ (idx+1UL) ^ (0x9e3779b97f4a7c15UL*(i+1UL));
}

static void
hash_from_idx( fd_hash_t * out,
               ulong       domain,
               ulong       idx ) {
  for( ulong i=0UL; i<4UL; i++ )
    out->ul[ i ] = 0x65a17b1ee5eed000UL ^ (domain<<48) ^ (idx+1UL) ^ (0xd6e8feb86659fd93UL*(i+1UL));
}

static void
model_init( fuzz_model_t * m ) {
  fd_memset( m, 0, sizeof(*m) );
  m->root = FUZZ_ROOT_BASE;
  for( ulong i=0UL; i<FUZZ_VTR_MAX; i++ ) {
    pubkey_from_idx( &m->voter[ i ].pubkey, i );
    m->voter[ i ].stake  = 1UL + 3UL*i;
    m->voter[ i ].active = 1;
    m->voter[ i ].bit    = i;
  }
}

static ulong
model_total_stake( fuzz_model_t const * m ) {
  ulong total = 0UL;
  for( ulong i=0UL; i<FUZZ_VTR_MAX; i++ )
    if( m->voter[ i ].active ) total += m->voter[ i ].stake;
  return fd_ulong_max( total, 1UL );
}

static votes_slot_model_t *
model_votes_slot_query( fuzz_model_t * m,
                        ulong          slot ) {
  for( ulong i=0UL; i<FUZZ_SLOT_MAX; i++ )
    if( m->votes_slot[ i ].present && m->votes_slot[ i ].slot==slot ) return &m->votes_slot[ i ];
  return NULL;
}

static votes_slot_model_t *
model_votes_slot_acquire( fuzz_model_t * m,
                          ulong          slot ) {
  votes_slot_model_t * s = model_votes_slot_query( m, slot );
  if( FD_LIKELY( s ) ) return s;

  for( ulong i=0UL; i<FUZZ_SLOT_MAX; i++ ) {
    s = &m->votes_slot[ i ];
    if( FD_LIKELY( !s->present ) ) {
      fd_memset( s, 0, sizeof(*s) );
      s->present = 1;
      s->slot    = slot;
      return s;
    }
  }

  FD_LOG_ERR(( "votes model slot capacity exhausted" ));
}

static votes_blk_model_t *
model_votes_blk_query( fuzz_model_t * m,
                       ulong          slot,
                       ulong          block_idx ) {
  votes_slot_model_t * s = model_votes_slot_query( m, slot );
  if( FD_UNLIKELY( !s ) ) return NULL;
  for( ulong i=0UL; i<s->blk_cnt; i++ )
    if( s->blk[ i ].block_idx==block_idx ) return &s->blk[ i ];
  return NULL;
}

static votes_blk_model_t *
model_votes_blk_acquire( fuzz_model_t * m,
                         ulong          slot,
                         ulong          block_idx ) {
  votes_slot_model_t * s = model_votes_slot_acquire( m, slot );
  votes_blk_model_t * b = model_votes_blk_query( m, slot, block_idx );
  if( FD_LIKELY( b ) ) return b;
  FD_TEST( s->blk_cnt<FUZZ_VTR_MAX );
  b = &s->blk[ s->blk_cnt++ ];
  fd_memset( b, 0, sizeof(*b) );
  b->block_idx = block_idx;
  return b;
}

static void
model_votes_prune( fuzz_model_t * m,
                   ulong          root ) {
  for( ulong i=0UL; i<FUZZ_SLOT_MAX; i++ )
    if( m->votes_slot[ i ].present && m->votes_slot[ i ].slot<root )
      fd_memset( &m->votes_slot[ i ], 0, sizeof(m->votes_slot[ i ]) );
  m->root = root;
}

static votes_blk_model_t *
model_votes_forward_best( fuzz_model_t * m,
                          ulong          slot,
                          uchar *        level ) {
  votes_slot_model_t * s = model_votes_slot_query( m, slot );
  votes_blk_model_t * best = NULL;
  uchar best_level = 0U;
  if( FD_LIKELY( s ) ) {
    for( ulong i=0UL; i<s->blk_cnt; i++ ) {
      uchar l = (uchar)(s->blk[ i ].flags >> 4);
      if( l>best_level ) {
        best       = &s->blk[ i ];
        best_level = l;
      }
    }
  }
  *level = best_level;
  return best;
}

static hfork_pair_model_t *
model_hfork_pair_query( fuzz_model_t * m,
                        ulong          block_idx,
                        ulong          bank_idx ) {
  for( ulong i=0UL; i<sizeof(m->hfork_pair)/sizeof(m->hfork_pair[0]); i++ ) {
    hfork_pair_model_t * p = &m->hfork_pair[ i ];
    if( p->present && p->block_idx==block_idx && p->bank_idx==bank_idx ) return p;
  }
  return NULL;
}

static hfork_pair_model_t *
model_hfork_pair_acquire( fuzz_model_t * m,
                          ulong          block_idx,
                          ulong          bank_idx ) {
  hfork_pair_model_t * p = model_hfork_pair_query( m, block_idx, bank_idx );
  if( FD_LIKELY( p ) ) return p;
  for( ulong i=0UL; i<sizeof(m->hfork_pair)/sizeof(m->hfork_pair[0]); i++ ) {
    p = &m->hfork_pair[ i ];
    if( FD_LIKELY( !p->present ) ) {
      fd_memset( p, 0, sizeof(*p) );
      p->present   = 1;
      p->block_idx = block_idx;
      p->bank_idx  = bank_idx;
      p->order     = ++m->order_seq;
      return p;
    }
  }
  FD_LOG_ERR(( "hfork model pair capacity exhausted" ));
}

static ulong
model_hfork_pair_cnt( fuzz_model_t const * m,
                      ulong                block_idx ) {
  ulong cnt = 0UL;
  for( ulong i=0UL; i<sizeof(m->hfork_pair)/sizeof(m->hfork_pair[0]); i++ )
    cnt += (ulong)(m->hfork_pair[ i ].present && m->hfork_pair[ i ].block_idx==block_idx);
  return cnt;
}

static void
model_hfork_remove_pair_if_empty( fuzz_model_t *      m,
                                  hfork_pair_model_t * p ) {
  ulong block_idx = p->block_idx;
  if( FD_LIKELY( p->stake ) ) return;
  fd_memset( p, 0, sizeof(*p) );

  /* fd_hfork removes the blk, including our recorded bank hash, when
     the last bank-hash matcher for that block is removed. */
  if( FD_UNLIKELY( !model_hfork_pair_cnt( m, block_idx ) ) )
    fd_memset( &m->our_bank[ block_idx ], 0, sizeof(m->our_bank[ block_idx ]) );
}

static int
model_hfork_compare_pair( fuzz_model_t const *       m,
                          hfork_pair_model_t const * p,
                          ulong                      total_stake ) {
  our_bank_model_t const * ours = &m->our_bank[ p->block_idx ];
  if( FD_UNLIKELY( !ours->known                         ) ) return FD_HFORK_SUCCESS;
  if( FD_UNLIKELY( p->stake*100UL < 52UL*total_stake    ) ) return FD_HFORK_SUCCESS;
  if( FD_UNLIKELY( ours->dead || ours->bank_idx!=p->bank_idx ) ) return FD_HFORK_ERR_MISMATCHED;
  return FD_HFORK_SUCCESS_MATCHED;
}

static int
model_hfork_compare_block( fuzz_model_t const * m,
                           ulong                block_idx,
                           ulong                total_stake ) {
  hfork_pair_model_t const * best = NULL;
  for( ulong i=0UL; i<sizeof(m->hfork_pair)/sizeof(m->hfork_pair[0]); i++ ) {
    hfork_pair_model_t const * p = &m->hfork_pair[ i ];
    if( FD_UNLIKELY( !p->present || p->block_idx!=block_idx ) ) continue;
    if( FD_UNLIKELY( !best || p->order<best->order ) ) best = p;
  }

  while( best ) {
    int cmp = model_hfork_compare_pair( m, best, total_stake );
    if( cmp ) return cmp;

    hfork_pair_model_t const * next = NULL;
    for( ulong i=0UL; i<sizeof(m->hfork_pair)/sizeof(m->hfork_pair[0]); i++ ) {
      hfork_pair_model_t const * p = &m->hfork_pair[ i ];
      if( FD_UNLIKELY( !p->present || p->block_idx!=block_idx || p->order<=best->order ) ) continue;
      if( FD_UNLIKELY( !next || p->order<next->order ) ) next = p;
    }
    best = next;
  }
  return FD_HFORK_SUCCESS;
}

static void
model_hfork_remove_vote( fuzz_model_t * m,
                         hfork_vote_t *  vote ) {
  hfork_pair_model_t * p = model_hfork_pair_query( m, vote->block_idx, vote->bank_idx );
  FD_TEST( p );
  FD_TEST( p->stake>=vote->stake );
  p->stake -= vote->stake;
  model_hfork_remove_pair_if_empty( m, p );
}

static int
model_hfork_voter_has_block( voter_model_t const * v,
                             ulong                 block_idx ) {
  for( ulong i=0UL; i<v->hfork_vote_cnt; i++ )
    if( v->hfork_vote[ i ].block_idx==block_idx ) return 1;
  return 0;
}

static int
model_hfork_count_vote( fuzz_model_t * m,
                        ulong          voter_idx,
                        ulong          block_idx,
                        ulong          bank_idx,
                        ulong          slot,
                        ulong          stake,
                        ulong          total_stake ) {
  if( FD_UNLIKELY( voter_idx>=FUZZ_VTR_MAX || !m->voter[ voter_idx ].active ) ) return FD_HFORK_ERR_UNKNOWN_VTR;

  voter_model_t * v = &m->voter[ voter_idx ];
  if( FD_UNLIKELY( model_hfork_voter_has_block( v, block_idx ) ) ) return FD_HFORK_ERR_ALREADY_VOTED;
  if( FD_UNLIKELY( v->hfork_vote_cnt && v->hfork_vote[ v->hfork_vote_cnt-1UL ].slot>=slot ) ) return FD_HFORK_ERR_VOTE_TOO_OLD;
  if( FD_UNLIKELY( !stake ) ) return FD_HFORK_SUCCESS;

  if( FD_UNLIKELY( v->hfork_vote_cnt==FUZZ_PER_VTR_MAX ) ) {
    model_hfork_remove_vote( m, &v->hfork_vote[ 0 ] );
    memmove( &v->hfork_vote[ 0 ], &v->hfork_vote[ 1 ], (FUZZ_PER_VTR_MAX-1UL)*sizeof(v->hfork_vote[0]) );
    v->hfork_vote_cnt--;
  }

  hfork_pair_model_t * p = model_hfork_pair_acquire( m, block_idx, bank_idx );
  p->stake += stake;
  p->order  = ++m->order_seq;

  v->hfork_vote[ v->hfork_vote_cnt++ ] = (hfork_vote_t) {
    .block_idx = block_idx,
    .bank_idx  = bank_idx,
    .slot      = slot,
    .stake     = stake
  };

  return model_hfork_compare_pair( m, p, total_stake );
}

static void
model_update_voters( fuzz_model_t * m,
                     ulong          mask ) {
  ulong kept_bits = 0UL;
  for( ulong i=0UL; i<FUZZ_VTR_MAX; i++ ) {
    if( (mask & (1UL<<i)) && m->voter[ i ].active )
      kept_bits |= 1UL << m->voter[ i ].bit;
  }

  for( ulong i=0UL; i<FUZZ_SLOT_MAX; i++ )
    if( m->votes_slot[ i ].present ) m->votes_slot[ i ].bits &= kept_bits;

  for( ulong i=0UL; i<FUZZ_VTR_MAX; i++ ) {
    voter_model_t * v = &m->voter[ i ];
    if( FD_LIKELY( mask & (1UL<<i) ) ) continue;
    if( FD_LIKELY( !v->active ) ) continue;

    while( v->hfork_vote_cnt ) {
      model_hfork_remove_vote( m, &v->hfork_vote[ 0 ] );
      memmove( &v->hfork_vote[ 0 ], &v->hfork_vote[ 1 ], (FUZZ_PER_VTR_MAX-1UL)*sizeof(v->hfork_vote[0]) );
      v->hfork_vote_cnt--;
    }
    v->active = 0;
  }

  ulong used_bits = kept_bits;
  for( ulong i=0UL; i<FUZZ_VTR_MAX; i++ ) {
    voter_model_t * v = &m->voter[ i ];
    if( FD_UNLIKELY( !(mask & (1UL<<i)) || v->active ) ) continue;

    ulong bit = 0UL;
    while( used_bits & (1UL<<bit) ) bit++;
    v->active         = 1;
    v->bit            = bit;
    v->hfork_vote_cnt = 0UL;
    used_bits        |= 1UL<<bit;
  }
}

static void
apply_update_voters( fd_votes_t *       votes,
                     fd_hfork_t *       hfork,
                     fuzz_model_t *     m,
                     fuzz_reader_t *    r ) {
  ulong mask = fuzz_bounded( r, 1UL<<FUZZ_VTR_MAX );

  fd_pubkey_t vote_accs[ FUZZ_VTR_MAX ];
  ulong cnt = 0UL;
  for( ulong i=0UL; i<FUZZ_VTR_MAX; i++ )
    if( mask & (1UL<<i) ) vote_accs[ cnt++ ] = m->voter[ i ].pubkey;

  fd_votes_update_voters( votes, vote_accs, cnt );
  fd_hfork_update_voters( hfork, vote_accs, cnt );
  model_update_voters( m, mask );

  FD_FUZZ_MUST_BE_COVERED;
}

static int
expected_votes_count( fuzz_model_t * m,
                      ulong          voter_idx,
                      ulong          slot,
                      ulong          block_idx,
                      ulong          stake ) {
  if( FD_UNLIKELY( slot >= m->root + FUZZ_SLOT_MAX ) ) return FD_VOTES_ERR_VOTE_TOO_NEW;
  if( FD_UNLIKELY( voter_idx>=FUZZ_VTR_MAX || !m->voter[ voter_idx ].active ) ) return FD_VOTES_ERR_UNKNOWN_VTR;

  voter_model_t const * v = &m->voter[ voter_idx ];
  votes_slot_model_t * s = model_votes_slot_query( m, slot );
  if( FD_UNLIKELY( s && (s->bits & (1UL<<v->bit)) ) ) return FD_VOTES_ERR_ALREADY_VOTED;

  s = model_votes_slot_acquire( m, slot );
  s->bits |= 1UL<<v->bit;
  votes_blk_model_t * b = model_votes_blk_acquire( m, slot, block_idx );
  b->stake += stake;
  return FD_VOTES_SUCCESS;
}

static void
check_votes_result( int expected,
                    int actual ) {
  FD_TEST( expected==actual );
  switch( actual ) {
    case FD_VOTES_SUCCESS:           FD_FUZZ_MUST_BE_COVERED; break;
    case FD_VOTES_ERR_VOTE_TOO_NEW:  FD_FUZZ_MUST_BE_COVERED; break;
    case FD_VOTES_ERR_UNKNOWN_VTR:   FD_FUZZ_MUST_BE_COVERED; break;
    case FD_VOTES_ERR_ALREADY_VOTED: FD_FUZZ_MUST_BE_COVERED; break;
    default: FD_LOG_ERR(( "unexpected votes result %d", actual ));
  }
}

static void
check_hfork_result( int expected,
                    int actual,
                    ulong stake ) {
  FD_TEST( expected==actual );
  switch( actual ) {
    case FD_HFORK_SUCCESS_MATCHED:   FD_FUZZ_MUST_BE_COVERED; break;
    case FD_HFORK_SUCCESS:
      if( FD_UNLIKELY( !stake ) ) FD_FUZZ_MUST_BE_COVERED;
      else                        FD_FUZZ_MUST_BE_COVERED;
      break;
    case FD_HFORK_ERR_MISMATCHED:    FD_FUZZ_MUST_BE_COVERED; break;
    case FD_HFORK_ERR_UNKNOWN_VTR:   FD_FUZZ_MUST_BE_COVERED; break;
    case FD_HFORK_ERR_ALREADY_VOTED: FD_FUZZ_MUST_BE_COVERED; break;
    case FD_HFORK_ERR_VOTE_TOO_OLD:  FD_FUZZ_MUST_BE_COVERED; break;
    default: FD_LOG_ERR(( "unexpected hfork result %d", actual ));
  }
}

static ulong
choose_slot( fuzz_model_t const * m,
             fuzz_reader_t *      r ) {
  ulong mode = fuzz_bounded( r, 8UL );
  if( FD_UNLIKELY( !mode ) ) return m->root + FUZZ_SLOT_MAX + fuzz_bounded( r, 4UL );
  return m->root + fuzz_bounded( r, FUZZ_SLOT_MAX );
}

static void
apply_vote( fd_votes_t *       votes,
            fd_hfork_t *       hfork,
            fuzz_model_t *     m,
            fuzz_reader_t *    r,
            int                use_last ) {
  ulong voter_idx;
  ulong slot;
  ulong block_idx;
  ulong bank_idx;

  if( FD_UNLIKELY( use_last && m->have_last_vote && m->last_slot>=m->root ) ) {
    voter_idx  = m->last_voter_idx;
    slot       = m->last_slot;
    block_idx  = m->last_block_idx;
    bank_idx   = m->last_bank_idx;
  } else {
    voter_idx = fuzz_bounded( r, FUZZ_VTR_MAX+2UL );
    slot      = choose_slot( m, r );
    block_idx = fuzz_bounded( r, FUZZ_BLOCK_MAX );
    bank_idx  = fuzz_bounded( r, FUZZ_BANK_MAX );

    if( FD_UNLIKELY( (fuzz_u8( r ) & 15U)==0U ) ) {
      voter_idx = fuzz_bounded( r, FUZZ_VTR_MAX );
      voter_model_t const * v = &m->voter[ voter_idx ];
      if( v->hfork_vote_cnt && v->hfork_vote[ v->hfork_vote_cnt-1UL ].slot>=m->root ) {
        ulong last_slot = v->hfork_vote[ v->hfork_vote_cnt-1UL ].slot;
        slot = last_slot - fd_ulong_min( fuzz_bounded( r, 2UL ), last_slot - m->root );
      }
    }
  }

  fd_pubkey_t vote_acc;
  if( FD_LIKELY( voter_idx<FUZZ_VTR_MAX ) ) vote_acc = m->voter[ voter_idx ].pubkey;
  else pubkey_from_idx( &vote_acc, 100UL + voter_idx );

  fd_hash_t block_id[ 1 ];
  fd_hash_t bank_hash[ 1 ];
  hash_from_idx( block_id,  0UL, block_idx );
  hash_from_idx( bank_hash, 1UL, bank_idx  );

  ulong stake = voter_idx<FUZZ_VTR_MAX ? m->voter[ voter_idx ].stake : fuzz_bounded( r, 32UL );

  int expected_votes = expected_votes_count( m, voter_idx, slot, block_idx, stake );
  int actual_votes   = fd_votes_count_vote( votes, &vote_acc, stake, slot, block_id );
  check_votes_result( expected_votes, actual_votes );

  if( FD_LIKELY( actual_votes==FD_VOTES_SUCCESS ) ) {
    fd_votes_blk_t * actual_blk = fd_votes_query( votes, slot, block_id );
    votes_blk_model_t * model_blk = model_votes_blk_query( m, slot, block_idx );
    FD_TEST( actual_blk );
    FD_TEST( model_blk );
    FD_TEST( actual_blk->stake==model_blk->stake );
  }

  ulong total_stake     = model_total_stake( m );
  int expected_hfork    = model_hfork_count_vote( m, voter_idx, block_idx, bank_idx, slot, stake, total_stake );
  int actual_hfork      = fd_hfork_count_vote( hfork, &vote_acc, block_id, bank_hash, slot, stake, total_stake );
  check_hfork_result( expected_hfork, actual_hfork, stake );

  m->have_last_vote = 1;
  m->last_voter_idx = voter_idx;
  m->last_slot      = slot;
  m->last_block_idx = block_idx;
  m->last_bank_idx  = bank_idx;
}

static void
apply_publish( fd_votes_t *    votes,
               fuzz_model_t *  m,
               fuzz_reader_t * r ) {
  ulong root = m->root + fuzz_bounded( r, 4UL );
  fd_votes_publish( votes, root );
  model_votes_prune( m, root );

  for( ulong i=0UL; i<FUZZ_SLOT_MAX; i++ ) {
    if( FD_UNLIKELY( m->votes_slot[ i ].present ) ) continue;
    ulong slot = root > i ? root - i - 1UL : 0UL;
    FD_TEST( !fd_votes_query( votes, slot, NULL ) );
    break;
  }

  FD_FUZZ_MUST_BE_COVERED;
}

static void
apply_stake_change( fuzz_model_t *  m,
                    fuzz_reader_t * r ) {
  ulong voter_idx = fuzz_bounded( r, FUZZ_VTR_MAX );
  m->voter[ voter_idx ].stake = fuzz_bounded( r, 64UL );
  FD_FUZZ_MUST_BE_COVERED;
}

static void
apply_record_bank_hash( fd_hfork_t *    hfork,
                        fuzz_model_t *  m,
                        fuzz_reader_t * r ) {
  ulong block_idx = fuzz_bounded( r, FUZZ_BLOCK_MAX );
  ulong bank_idx  = fuzz_bounded( r, FUZZ_BANK_MAX );
  int   dead      = !(fuzz_u8( r ) & 3U);

  fd_hash_t block_id[ 1 ];
  fd_hash_t bank_hash[ 1 ];
  hash_from_idx( block_id,  0UL, block_idx );
  hash_from_idx( bank_hash, 1UL, bank_idx  );

  m->our_bank[ block_idx ].known    = 1;
  m->our_bank[ block_idx ].dead     = dead;
  m->our_bank[ block_idx ].bank_idx = bank_idx;

  ulong total_stake  = model_total_stake( m );
  int expected       = model_hfork_compare_block( m, block_idx, total_stake );
  int actual         = fd_hfork_record_our_bank_hash( hfork, block_id, dead ? NULL : bank_hash, total_stake );
  check_hfork_result( expected, actual, 1UL );
}

static void
apply_votes_query( fd_votes_t *    votes,
                   fuzz_model_t *  m,
                   fuzz_reader_t * r ) {
  ulong slot      = m->root + fuzz_bounded( r, FUZZ_SLOT_MAX );
  ulong block_idx = fuzz_bounded( r, FUZZ_BLOCK_MAX );
  fd_hash_t block_id[ 1 ];
  hash_from_idx( block_id, 0UL, block_idx );

  fd_votes_blk_t * actual = fd_votes_query( votes, slot, block_id );
  votes_blk_model_t * expected = model_votes_blk_query( m, slot, block_idx );
  FD_TEST( (!actual)==(!expected) );
  if( FD_LIKELY( actual ) ) {
    FD_TEST( actual->stake==expected->stake );
    FD_TEST( actual->flags==expected->flags );
    FD_FUZZ_MUST_BE_COVERED;
  }

  uchar level = 0U;
  votes_blk_model_t * best = model_votes_forward_best( m, slot, &level );
  actual = fd_votes_query( votes, slot, NULL );
  if( FD_UNLIKELY( !best ) ) {
    FD_TEST( !actual );
    FD_FUZZ_MUST_BE_COVERED;
  } else {
    FD_TEST( actual );
    FD_TEST( (actual->flags >> 4)==level );
    FD_FUZZ_MUST_BE_COVERED;
  }
}

static void
apply_set_forward_flags( fd_votes_t *    votes,
                         fuzz_model_t *  m,
                         fuzz_reader_t * r ) {
  ulong slot      = m->root + fuzz_bounded( r, FUZZ_SLOT_MAX );
  ulong block_idx = fuzz_bounded( r, FUZZ_BLOCK_MAX );
  uchar flags     = fuzz_u8( r );

  fd_hash_t block_id[ 1 ];
  hash_from_idx( block_id, 0UL, block_idx );

  fd_votes_blk_t * actual = fd_votes_query( votes, slot, block_id );
  votes_blk_model_t * expected = model_votes_blk_query( m, slot, block_idx );
  FD_TEST( (!actual)==(!expected) );
  if( FD_LIKELY( actual ) ) {
    actual->flags    = flags;
    expected->flags  = flags;
    FD_FUZZ_MUST_BE_COVERED;
  }
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

  ulong votes_fp = FD_ULONG_ALIGN_UP( fd_votes_footprint( FUZZ_SLOT_MAX, FUZZ_VTR_MAX ), fd_votes_align() );
  ulong hfork_fp = FD_ULONG_ALIGN_UP( fd_hfork_footprint( FUZZ_PER_VTR_MAX, FUZZ_VTR_MAX ), fd_hfork_align() );
  fuzz_votes_mem = aligned_alloc( fd_votes_align(), votes_fp );
  fuzz_hfork_mem = aligned_alloc( fd_hfork_align(), hfork_fp );
  FD_TEST( fuzz_votes_mem );
  FD_TEST( fuzz_hfork_mem );

  atexit( fuzz_cleanup );
  return 0;
}

int
LLVMFuzzerTestOneInput( uchar const * data,
                        ulong         size ) {
  fuzz_reader_t r = {
    .data    = data,
    .data_sz = size,
    .off     = 0UL,
    .salt    = 0x48666f726b566f74UL ^ size
  };

  fd_votes_t * votes = fd_votes_join( fd_votes_new( fuzz_votes_mem, FUZZ_SLOT_MAX, FUZZ_VTR_MAX, 0xdecafbadUL ) );
  fd_hfork_t * hfork = fd_hfork_join( fd_hfork_new( fuzz_hfork_mem, FUZZ_PER_VTR_MAX, FUZZ_VTR_MAX, 0xbadc0feeUL ) );
  FD_TEST( votes );
  FD_TEST( hfork );

  fuzz_model_t * model = fuzz_model;
  model_init( model );

  fd_pubkey_t initial_vote_accs[ FUZZ_VTR_MAX ];
  for( ulong i=0UL; i<FUZZ_VTR_MAX; i++ ) initial_vote_accs[ i ] = model->voter[ i ].pubkey;
  fd_votes_update_voters( votes, initial_vote_accs, FUZZ_VTR_MAX );
  fd_hfork_update_voters( hfork, initial_vote_accs, FUZZ_VTR_MAX );
  fd_votes_publish( votes, model->root );

  ulong action_cnt = 1UL + fuzz_bounded( &r, FUZZ_ACTION_MAX );
  for( ulong i=0UL; i<action_cnt; i++ ) {
    switch( fuzz_bounded( &r, 8UL ) ) {
      case 0UL: apply_vote             ( votes, hfork, model, &r, 0 ); break;
      case 1UL: apply_vote             ( votes, hfork, model, &r, 1 ); break;
      case 2UL: apply_update_voters    ( votes, hfork, model, &r    ); break;
      case 3UL: apply_publish          ( votes,        model, &r    ); break;
      case 4UL: apply_stake_change     (               model, &r    ); break;
      case 5UL: apply_record_bank_hash (        hfork, model, &r    ); break;
      case 6UL: apply_votes_query      ( votes,        model, &r    ); break;
      case 7UL: apply_set_forward_flags( votes,        model, &r    ); break;
      default: FD_LOG_ERR(( "unreachable action" ));
    }
  }

  fd_votes_delete( fd_votes_leave( votes ) );
  fd_hfork_delete( fd_hfork_leave( hfork ) );

  return 0;
}
