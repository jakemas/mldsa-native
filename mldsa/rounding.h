/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef ROUNDING_H
#define ROUNDING_H

#include <stdint.h>
#include "params.h"

#define power2round MLD_NAMESPACE(power2round)
int32_t power2round(int32_t *a0, int32_t a);

#define decompose MLD_NAMESPACE(decompose)
int32_t decompose(int32_t *a0, int32_t a);

#define make_hint MLD_NAMESPACE(make_hint)
unsigned int make_hint(int32_t a0, int32_t a1);

#define use_hint MLD_NAMESPACE(use_hint)
int32_t use_hint(int32_t a, unsigned int hint);

#endif
