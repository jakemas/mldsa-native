/*
 * Copyright (c) 2025 The mldsa-native project authors
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../mldsa/ntt.h"
#include "../mldsa/randombytes.h"
#include "hal.h"

#define NWARMUP 50
#define NITERATIONS 300
#define NTESTS 20

static int cmp_uint64_t(const void *a, const void *b)
{
  return (int)((*((const uint64_t *)a)) - (*((const uint64_t *)b)));
}

#define BENCH(txt, code)                                \
  for (i = 0; i < NTESTS; i++)                          \
  {                                                     \
    randombytes((uint8_t *)data0, sizeof(data0));       \
    for (j = 0; j < NWARMUP; j++)                       \
    {                                                   \
      code;                                             \
    }                                                   \
                                                        \
    t0 = get_cyclecounter();                            \
    for (j = 0; j < NITERATIONS; j++)                   \
    {                                                   \
      code;                                             \
    }                                                   \
    t1 = get_cyclecounter();                            \
    (cyc)[i] = t1 - t0;                                 \
  }                                                     \
  qsort((cyc), NTESTS, sizeof(uint64_t), cmp_uint64_t); \
  printf(txt " cycles=%" PRIu64 "\n", (cyc)[NTESTS >> 1] / NITERATIONS);

static int bench(void)
{
  int32_t data0[256];
  uint64_t cyc[NTESTS];
  unsigned i, j;
  uint64_t t0, t1;

  /* ntt */
  BENCH("ntt", ntt(data0))

  return 0;
}

int main(void)
{
  enable_cyclecounter();
  bench();
  disable_cyclecounter();

  return 0;
}
