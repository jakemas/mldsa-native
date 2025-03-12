/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef NTT_H
#define NTT_H

#include <stdint.h>
#include "params.h"

#define ntt MLD_NAMESPACE(ntt)
void ntt(int32_t a[N]);

#define invntt_tomont MLD_NAMESPACE(invntt_tomont)
void invntt_tomont(int32_t a[N]);

#endif
