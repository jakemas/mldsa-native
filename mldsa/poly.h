/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef POLY_H
#define POLY_H

#include <stdint.h>
#include "cbmc.h"
#include "params.h"

typedef struct
{
  int32_t coeffs[N];
} poly;

#define poly_reduce MLD_NAMESPACE(poly_reduce)
void poly_reduce(poly *a);
#define poly_caddq MLD_NAMESPACE(poly_caddq)
void poly_caddq(poly *a);

#define poly_add MLD_NAMESPACE(poly_add)
void poly_add(poly *c, const poly *a, const poly *b)
__contract__(
  requires(memory_no_alias(c, sizeof(poly)))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(memory_no_alias(b, sizeof(poly)))
  requires(forall(k0, 0, N, (int64_t) a->coeffs[k0] + b->coeffs[k0] <= INT32_MAX))
  requires(forall(k1, 0, N, (int64_t) a->coeffs[k1] + b->coeffs[k1] >= INT32_MIN))
  ensures(forall(k, 0, N, c->coeffs[k] == a->coeffs[k] + b->coeffs[k]))
  assigns(memory_slice(c, sizeof(poly)))
);

#define poly_sub MLD_NAMESPACE(poly_sub)
void poly_sub(poly *c, const poly *a, const poly *b);

#define poly_shiftl MLD_NAMESPACE(poly_shiftl)
void poly_shiftl(poly *a)
__contract__(
  requires(memory_no_alias(a, sizeof(poly)))
  requires(array_abs_bound(a->coeffs, 0, N, 1 << (31 - D) - 1))
  assigns(memory_slice(a, sizeof(poly)))
);

#define poly_ntt MLD_NAMESPACE(poly_ntt)
void poly_ntt(poly *a);
#define poly_invntt_tomont MLD_NAMESPACE(poly_invntt_tomont)
void poly_invntt_tomont(poly *a);
#define poly_pointwise_montgomery MLD_NAMESPACE(poly_pointwise_montgomery)
void poly_pointwise_montgomery(poly *c, const poly *a, const poly *b);

#define poly_power2round MLD_NAMESPACE(poly_power2round)
void poly_power2round(poly *a1, poly *a0, const poly *a);
#define poly_decompose MLD_NAMESPACE(poly_decompose)
void poly_decompose(poly *a1, poly *a0, const poly *a);
#define poly_make_hint MLD_NAMESPACE(poly_make_hint)
unsigned int poly_make_hint(poly *h, const poly *a0, const poly *a1);
#define poly_use_hint MLD_NAMESPACE(poly_use_hint)
void poly_use_hint(poly *b, const poly *a, const poly *h);

#define poly_chknorm MLD_NAMESPACE(poly_chknorm)
int poly_chknorm(const poly *a, int32_t B);
#define poly_uniform MLD_NAMESPACE(poly_uniform)
void poly_uniform(poly *a, const uint8_t seed[SEEDBYTES], uint16_t nonce);
#define poly_uniform_eta MLD_NAMESPACE(poly_uniform_eta)
void poly_uniform_eta(poly *a, const uint8_t seed[CRHBYTES], uint16_t nonce);
#define poly_uniform_gamma1 MLD_NAMESPACE(poly_uniform_gamma1)
void poly_uniform_gamma1(poly *a, const uint8_t seed[CRHBYTES], uint16_t nonce);
#define poly_challenge MLD_NAMESPACE(poly_challenge)
void poly_challenge(poly *c, const uint8_t seed[CTILDEBYTES]);

#define polyeta_pack MLD_NAMESPACE(polyeta_pack)
void polyeta_pack(uint8_t *r, const poly *a)
__contract__(
  requires(memory_no_alias(r, POLYETA_PACKEDBYTES))
  requires(memory_no_alias(a, sizeof(poly)))
  requires(forall(k0, 0, N, a->coeffs[k0] <= ETA))
  requires(forall(k1, 0, N, a->coeffs[k1] >= -ETA))
  assigns(object_whole(r))
);

#define polyeta_unpack MLD_NAMESPACE(polyeta_unpack)
void polyeta_unpack(poly *r, const uint8_t *a);

#define polyt1_pack MLD_NAMESPACE(polyt1_pack)
void polyt1_pack(uint8_t *r, const poly *a);
#define polyt1_unpack MLD_NAMESPACE(polyt1_unpack)
void polyt1_unpack(poly *r, const uint8_t *a);

#define polyt0_pack MLD_NAMESPACE(polyt0_pack)
void polyt0_pack(uint8_t *r, const poly *a);
#define polyt0_unpack MLD_NAMESPACE(polyt0_unpack)
void polyt0_unpack(poly *r, const uint8_t *a);

#define polyz_pack MLD_NAMESPACE(polyz_pack)
void polyz_pack(uint8_t *r, const poly *a);
#define polyz_unpack MLD_NAMESPACE(polyz_unpack)
void polyz_unpack(poly *r, const uint8_t *a);

#define polyw1_pack MLD_NAMESPACE(polyw1_pack)
void polyw1_pack(uint8_t *r, const poly *a);

#endif
