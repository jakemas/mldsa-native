/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <string.h>

#include "common.h"
#include "packing.h"
#include "poly.h"
#include "polyvec.h"

void pack_pk(uint8_t pk[CRYPTO_PUBLICKEYBYTES],
             const uint8_t rho[MLDSA_SEEDBYTES], const polyveck *t1)
{
  unsigned int i;

  memcpy(pk, rho, MLDSA_SEEDBYTES);
  pk += MLDSA_SEEDBYTES;

  for (i = 0; i < MLDSA_K; ++i)
  {
    polyt1_pack(pk + i * MLDSA_POLYT1_PACKEDBYTES, &t1->vec[i]);
  }
}

void unpack_pk(uint8_t rho[MLDSA_SEEDBYTES], polyveck *t1,
               const uint8_t pk[CRYPTO_PUBLICKEYBYTES])
{
  unsigned int i;

  memcpy(rho, pk, MLDSA_SEEDBYTES);
  pk += MLDSA_SEEDBYTES;

  for (i = 0; i < MLDSA_K; ++i)
  {
    polyt1_unpack(&t1->vec[i], pk + i * MLDSA_POLYT1_PACKEDBYTES);
  }
}

void pack_sk(uint8_t sk[CRYPTO_SECRETKEYBYTES],
             const uint8_t rho[MLDSA_SEEDBYTES],
             const uint8_t tr[MLDSA_TRBYTES],
             const uint8_t key[MLDSA_SEEDBYTES], const polyveck *t0,
             const polyvecl *s1, const polyveck *s2)
{
  memcpy(sk, rho, MLDSA_SEEDBYTES);
  sk += MLDSA_SEEDBYTES;

  memcpy(sk, key, MLDSA_SEEDBYTES);
  sk += MLDSA_SEEDBYTES;

  memcpy(sk, tr, MLDSA_TRBYTES);
  sk += MLDSA_TRBYTES;

  polyvecl_pack_eta(sk, s1);
  sk += MLDSA_L * MLDSA_POLYETA_PACKEDBYTES;

  polyveck_pack_eta(sk, s2);
  sk += MLDSA_K * MLDSA_POLYETA_PACKEDBYTES;

  polyveck_pack_t0(sk, t0);
}

void unpack_sk(uint8_t rho[MLDSA_SEEDBYTES], uint8_t tr[MLDSA_TRBYTES],
               uint8_t key[MLDSA_SEEDBYTES], polyveck *t0, polyvecl *s1,
               polyveck *s2, const uint8_t sk[CRYPTO_SECRETKEYBYTES])
{
  memcpy(rho, sk, MLDSA_SEEDBYTES);
  sk += MLDSA_SEEDBYTES;

  memcpy(key, sk, MLDSA_SEEDBYTES);
  sk += MLDSA_SEEDBYTES;

  memcpy(tr, sk, MLDSA_TRBYTES);
  sk += MLDSA_TRBYTES;

  polyvecl_unpack_eta(s1, sk);
  sk += MLDSA_L * MLDSA_POLYETA_PACKEDBYTES;

  polyveck_unpack_eta(s2, sk);
  sk += MLDSA_K * MLDSA_POLYETA_PACKEDBYTES;

  polyveck_unpack_t0(t0, sk);
}

void pack_sig(uint8_t sig[CRYPTO_BYTES], const uint8_t c[MLDSA_CTILDEBYTES],
              const polyvecl *z, const polyveck *h,
              const unsigned int number_of_hints)
{
  unsigned int i, j, k;

  memcpy(sig, c, MLDSA_CTILDEBYTES);
  sig += MLDSA_CTILDEBYTES;

  polyvecl_pack_z(sig, z);
  sig += MLDSA_L * MLDSA_POLYZ_PACKEDBYTES;

  /* Encode hints h */

  /* The final section of sig[] is MLDSA_POLYVECH_PACKEDBYTES long, where
   * MLDSA_POLYVECH_PACKEDBYTES = MLDSA_OMEGA + MLDSA_K
   *
   * The first OMEGA bytes record the index numbers of the coefficients
   * that are not equal to 0
   *
   * The final K bytes record a running tally of the number of hints
   * coming from each of the K polynomials in h.
   *
   * The pre-condition tells us that number_of_hints <= OMEGA, so some
   * bytes may not be written, so we initialize all of them to zero
   * to start.
   */
  memset(sig, 0, MLDSA_POLYVECH_PACKEDBYTES);

  k = 0;
  /* For each polynomial in h... */
  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, j, k, memory_slice(sig, MLDSA_POLYVECH_PACKEDBYTES))
    invariant(i <= MLDSA_K)
    invariant(k <= number_of_hints)
    invariant(number_of_hints <= MLDSA_OMEGA)
  )
  {
    /* For each coefficient in that polynomial, record it as as hint */
    /* if its value is not zero */
    for (j = 0; j < MLDSA_N; ++j)
    __loop__(
      assigns(j, k, memory_slice(sig, MLDSA_POLYVECH_PACKEDBYTES))
      invariant(i <= MLDSA_K)
      invariant(j <= MLDSA_N)
      invariant(k <= number_of_hints)
      invariant(number_of_hints <= MLDSA_OMEGA)
    )
    {
      /* The reference implementation implicitly relies on the total */
      /* number of hints being less than OMEGA, assuming h is valid. */
      /* In mldsa-native, we check this explicitly to ease proof of  */
      /* type safety.                                                */
      if (h->vec[i].coeffs[j] != 0 && k < number_of_hints)
      {
        /* The enclosing if condition AND the loop invariant infer  */
        /* that k < MLDSA_OMEGA, so writing to sig[k] is safe and k */
        /* can be incremented.                                      */
        sig[k++] = j;
      }
    }
    /* Having recorded all the hints for this polynomial, also   */
    /* record the running tally into the correct "slot" for that */
    /* coefficient in the final K bytes                          */
    sig[MLDSA_OMEGA + i] = k;
  }
}

/*************************************************
 * Name:        unpack_hints
 *
 * Description: Unpack raw hint bytes into a polyveck
 *              struct
 *
 * Arguments:   - polyveck *h: pointer to output hint vector h
 *              - const uint8_t packed_hints[MLDSA_POLYVECH_PACKEDBYTES]:
 *                raw hint bytes
 *
 * Returns 1 in case of malformed hints; otherwise 0.
 **************************************************/
static int unpack_hints(polyveck *h,
                        const uint8_t packed_hints[MLDSA_POLYVECH_PACKEDBYTES])
__contract__(
  requires(memory_no_alias(packed_hints, MLDSA_POLYVECH_PACKEDBYTES))
  requires(memory_no_alias(h, sizeof(polyveck)))
  assigns(object_whole(h))
  /* All returned coefficients are either 0 or 1 */
  ensures(forall(k1, 0, MLDSA_K,
    array_bound(h->vec[k1].coeffs, 0, MLDSA_N, 0, 2)))
  ensures(return_value >= 0 && return_value <= 1)
)
{
  unsigned int i, j;
  unsigned int old_hint_count;

  /* Set all coefficients of all polynomials to 0.    */
  /* Only those that are actually non-zero hints will */
  /* be overwritten below.                            */
  memset(h, 0, sizeof(polyveck));

  old_hint_count = 0;
  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    invariant(i <= MLDSA_K)
    /* Maintain the post-condition */
    invariant(forall(k1, 0, MLDSA_K, array_bound(h->vec[k1].coeffs, 0, MLDSA_N, 0, 2)))
  )
  {
    /* Grab the hint count for the i'th polynomial */
    const unsigned int new_hint_count = packed_hints[MLDSA_OMEGA + i];

    /* new_hint_count must increase or stay the same, but also remain */
    /* less than or equal to MLDSA_OMEGA                              */
    if (new_hint_count < old_hint_count || new_hint_count > MLDSA_OMEGA)
    {
      /* Error - new_hint_count is invalid */
      return 1;
    }

    /* If new_hint_count == old_hint_count, then this polynomial has */
    /* zero hints, so this loop executes zero times and we move      */
    /* straight on to the next polynomial.                           */
    for (j = old_hint_count; j < new_hint_count; ++j)
    __loop__(
        invariant(i <= MLDSA_K)
        /* Maintain the post-condition */
        invariant(forall(k1, 0, MLDSA_K, array_bound(h->vec[k1].coeffs, 0, MLDSA_N, 0, 2)))
      )
    {
      const uint8_t this_hint_index = packed_hints[j];

      /* Coefficients must be ordered for strong unforgeability */
      if (j > old_hint_count && this_hint_index <= packed_hints[j - 1])
      {
        return 1;
      }
      h->vec[i].coeffs[this_hint_index] = 1;
    }

    old_hint_count = new_hint_count;
  }

  /* Extra indices must be zero for strong unforgeability */
  for (j = old_hint_count; j < MLDSA_OMEGA; ++j)
  __loop__(
    invariant(j <= MLDSA_OMEGA)
    /* Maintain the post-condition */
    invariant(forall(k1, 0, MLDSA_K, array_bound(h->vec[k1].coeffs, 0, MLDSA_N, 0, 2)))
  )
  {
    if (packed_hints[j] != 0)
    {
      return 1;
    }
  }

  return 0;
}

int unpack_sig(uint8_t c[MLDSA_CTILDEBYTES], polyvecl *z, polyveck *h,
               const uint8_t sig[CRYPTO_BYTES])
{
  memcpy(c, sig, MLDSA_CTILDEBYTES);
  sig += MLDSA_CTILDEBYTES;

  polyvecl_unpack_z(z, sig);
  sig += MLDSA_L * MLDSA_POLYZ_PACKEDBYTES;

  return unpack_hints(h, sig);
}
