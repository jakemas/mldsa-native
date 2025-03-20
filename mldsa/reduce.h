/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef REDUCE_H
#define REDUCE_H

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

#define MONT -4186625  // 2^32 % Q
#define QINV 58728449  // q^(-1) mod 2^32
#define REDUCE_DOMAIN_MAX (INT32_MAX - (1 << 22))
#define REDUCE_RANGE_MAX 6283009

#define montgomery_reduce MLD_NAMESPACE(montgomery_reduce)
int32_t montgomery_reduce(int64_t a);

#define reduce32 MLD_NAMESPACE(reduce32)
int32_t reduce32(int32_t a)
__contract__(
  requires(a <= REDUCE_DOMAIN_MAX)
  ensures(return_value >= -REDUCE_RANGE_MAX)
  ensures(return_value <   REDUCE_RANGE_MAX)
  ensures((return_value - a) % Q == 0)
);

#define caddq MLD_NAMESPACE(caddq)
int32_t caddq(int32_t a);

#define freeze MLD_NAMESPACE(freeze)
int32_t freeze(int32_t a);

#endif
