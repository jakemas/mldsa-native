/*
 * Copyright (c) 2025 The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef CONFIG_H
#define CONFIG_H

// #define MLD_MODE 2
#define MLD_RANDOMIZED_SIGNING
// #define USE_RDPMC
// #define DBENCH

#ifndef MLD_MODE
#define MLD_MODE 2
#endif

#if MLD_MODE == 2
#define CRYPTO_ALGNAME "ML-DSA-44"
#define MLD_NAMESPACETOP MLD_44_ref
#define MLD_NAMESPACE(s) MLD_44_ref_##s
#elif MLD_MODE == 3
#define CRYPTO_ALGNAME "ML-DSA-65"
#define MLD_NAMESPACETOP MLD_65_ref
#define MLD_NAMESPACE(s) MLD_65_ref_##s
#elif MLD_MODE == 5
#define CRYPTO_ALGNAME "ML-DSA-87"
#define MLD_NAMESPACETOP MLD_87_ref
#define MLD_NAMESPACE(s) MLD_87_ref_##s
#endif

#endif
