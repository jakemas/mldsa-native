// Copyright (c) 2025 The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include "params.h"
#include "poly.h"

void harness(void)
{
  poly *a;
  poly_invntt_tomont(a);
}
