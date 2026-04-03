/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [REF_AVX2]
 *   CRYSTALS-Dilithium optimized AVX2 implementation
 *   Bai, Ducas, Kiltz, Lepoint, Lyubashevsky, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/dilithium/tree/master/avx2
 */

/*
 * This file is derived from the public domain
 * AVX2 Dilithium implementation @[REF_AVX2].
 */


/*
 * WARNING: This file is auto-derived from the mldsa-native source file
 *   dev/x86_64/src/rej_uniform_avx2.S using scripts/simpasm. Do not modify it directly.
 */

#if defined(__ELF__)
.section .note.GNU-stack,"",@progbits
#endif

.text
.balign 4
#ifdef __APPLE__
.global _PQCP_MLDSA_NATIVE_MLDSA44_mld_rej_uniform_avx2
_PQCP_MLDSA_NATIVE_MLDSA44_mld_rej_uniform_avx2:
#else
.global PQCP_MLDSA_NATIVE_MLDSA44_mld_rej_uniform_avx2
PQCP_MLDSA_NATIVE_MLDSA44_mld_rej_uniform_avx2:
#endif

        .cfi_startproc
        endbr64
        movabs $0xff050403ff020100,%r10

        vmovq  %r10,%xmm0
        movabs $0xff0b0a09ff080706,%r10

        vpinsrq $0x1,%r10,%xmm0,%xmm0
        movabs $0xff090807ff060504,%r10

        vmovq  %r10,%xmm3
        movabs $0xff0f0e0dff0c0b0a,%r10

        vpinsrq $0x1,%r10,%xmm3,%xmm3
        vinserti128 $0x1,%xmm3,%ymm0,%ymm0
        mov    $0x7fffff,%r8d
        vmovd  %r8d,%xmm1
        vpbroadcastd %xmm1,%ymm1
        mov    $0x7fe001,%r8d
        vmovd  %r8d,%xmm2
        vpbroadcastd %xmm2,%ymm2
        xor    %eax,%eax
        xor    %ecx,%ecx

Lmld_rej_uniform_avx2_loop:
        cmp    $0xf8,%eax
        ja     Lmld_rej_uniform_avx2_scalar
        cmp    $0x328,%ecx
        ja     Lmld_rej_uniform_avx2_scalar
        vmovdqu (%rsi,%rcx,1),%ymm3
        add    $0x18,%ecx
        vpermq $0x94,%ymm3,%ymm3
        vpshufb %ymm0,%ymm3,%ymm3
        vpand  %ymm1,%ymm3,%ymm3
        vpsubd %ymm2,%ymm3,%ymm4
        vmovmskps %ymm4,%r8d
        popcnt %r8d,%r9d
        vmovq  (%rdx,%r8,8),%xmm4
        vpmovzxbd %xmm4,%ymm4
        vpermd %ymm3,%ymm4,%ymm3
        vmovdqu %ymm3,(%rdi,%rax,4)
        add    %r9d,%eax
        jmp    Lmld_rej_uniform_avx2_loop

Lmld_rej_uniform_avx2_scalar:
        cmp    $0x100,%eax
        jae    Lmld_rej_uniform_avx2_done
        cmp    $0x345,%ecx
        ja     Lmld_rej_uniform_avx2_done
        movzwl (%rsi,%rcx,1),%r8d
        movzbl 0x2(%rsi,%rcx,1),%r9d
        shl    $0x10,%r9d
        or     %r9d,%r8d
        and    $0x7fffff,%r8d
        add    $0x3,%ecx
        cmp    $0x7fe001,%r8d
        jae    Lmld_rej_uniform_avx2_scalar
        mov    %r8d,(%rdi,%rax,4)
        add    $0x1,%eax
        jmp    Lmld_rej_uniform_avx2_scalar

Lmld_rej_uniform_avx2_done:
        vzeroupper
        ret
        .cfi_endproc
