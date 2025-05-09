// Copyright (c) 2025 The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0

#include "packing.h"

int unpack_hints(polyveck *h,
                 const uint8_t packed_hints[MLDSA_POLYVECH_PACKEDBYTES]);

void harness(void)
{
  uint8_t *sig;
  polyveck *h;
  int r;
  r = unpack_hints(h, sig);
}
