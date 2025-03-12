/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdio.h>
#include <string.h>

#include "nistrng.h"

#include "../mldsa/api.h"
#include "../mldsa/randombytes.h"



#if MLD_MODE == 2
#define CRYPTO_ALGNAME "ML-DSA-44"
#elif MLD_MODE == 3
#define CRYPTO_ALGNAME "ML-DSA-65"
#elif MLD_MODE == 5
#define CRYPTO_ALGNAME "ML-DSA-87"
#endif

static void fprintBstr(FILE *fp, const char *S, const uint8_t *A, size_t L)
{
  size_t i;
  fprintf(fp, "%s", S);
  for (i = 0; i < L; i++)
  {
    fprintf(fp, "%02X", A[i]);
  }
  if (L == 0)
  {
    fprintf(fp, "00");
  }
  fprintf(fp, "\n");
}

int main(void)
{
  uint8_t entropy_input[48];
  uint8_t seed[48];
  FILE *fh = stdout;
  uint8_t public_key[CRYPTO_PUBLICKEYBYTES];
  uint8_t secret_key[CRYPTO_SECRETKEYBYTES];
  size_t mlen = 33;
  size_t smlen, mlen1;
  uint8_t m[33];
  uint8_t sm[33 + CRYPTO_BYTES];
  int rc;

  for (uint8_t i = 0; i < 48; i++)
  {
    entropy_input[i] = i;
  }

  nist_kat_init(entropy_input, NULL, 256);

  fprintf(fh, "count = 0\n");
  randombytes(seed, 48);
  fprintBstr(fh, "seed = ", seed, 48);

  fprintf(fh, "mlen = 33\n");

  randombytes(m, mlen);
  fprintBstr(fh, "msg = ", m, mlen);

  nist_kat_init(seed, NULL, 256);

  rc = crypto_sign_keypair(public_key, secret_key);
  if (rc != 0)
  {
    fprintf(stderr, "[kat_kem] %s ERROR: crypto_kem_keypair failed!\n",
            CRYPTO_ALGNAME);
    return -1;
  }
  fprintBstr(fh, "pk = ", public_key, CRYPTO_PUBLICKEYBYTES);
  fprintBstr(fh, "sk = ", secret_key, CRYPTO_SECRETKEYBYTES);

  rc = crypto_sign(sm, &smlen, m, mlen, NULL, 0, secret_key);
  if (rc != 0)
  {
    fprintf(stderr, "[kat_kem] %s ERROR: crypto_sign failed!\n",
            CRYPTO_ALGNAME);
    return -2;
  }
  fprintf(fh, "smlen = %zu\n", smlen);
  fprintBstr(fh, "sm = ", sm, smlen);

  rc = crypto_sign_open(sm, &mlen1, sm, smlen, NULL, 0, public_key);
  if (rc != 0)
  {
    fprintf(stderr, "[kat_kem] %s ERROR: crypto_sign_open failed!\n",
            CRYPTO_ALGNAME);
    return -3;
  }

  if (mlen != mlen1)
  {
    printf("crypto_sign_open returned bad 'mlen': got <%zu>, expected <%zu>\n",
           mlen1, mlen);
    return -4;
  }
  if (memcmp(m, sm, mlen))
  {
    printf("crypto_sign_open returned bad 'm' value\n");
    return -5;
  }
  return 0;
}
