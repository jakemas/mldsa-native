/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef MLD_SYMMETRIC_H
#define MLD_SYMMETRIC_H

#include <stdint.h>

#include "fips202/fips202.h"

typedef keccak_state stream128_state;
typedef keccak_state stream256_state;

#define mldsa_shake128_stream_init MLD_NAMESPACE(mldsa_shake128_stream_init)
void mldsa_shake128_stream_init(keccak_state *state,
                                const uint8_t seed[MLDSA_SEEDBYTES],
                                uint16_t nonce);

#define mldsa_shake256_stream_init MLD_NAMESPACE(mldsa_shake256_stream_init)
void mldsa_shake256_stream_init(keccak_state *state,
                                const uint8_t seed[MLDSA_CRHBYTES],
                                uint16_t nonce);

#define STREAM128_BLOCKBYTES SHAKE128_RATE
#define STREAM256_BLOCKBYTES SHAKE256_RATE

#define stream128_init(STATE, SEED, NONCE) \
  mldsa_shake128_stream_init(STATE, SEED, NONCE)
#define stream128_squeezeblocks(OUT, OUTBLOCKS, STATE) \
  shake128_squeezeblocks(OUT, OUTBLOCKS, STATE)
#define stream256_init(STATE, SEED, NONCE) \
  mldsa_shake256_stream_init(STATE, SEED, NONCE)
#define stream256_squeezeblocks(OUT, OUTBLOCKS, STATE) \
  shake256_squeezeblocks(OUT, OUTBLOCKS, STATE)

#endif /* !MLD_SYMMETRIC_H */
