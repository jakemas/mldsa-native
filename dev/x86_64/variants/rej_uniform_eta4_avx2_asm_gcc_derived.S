/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *
 * Hand-written AVX2 assembly for rej_uniform_eta4 (eta=4 rejection sampling).
 * The instruction sequence below was derived from gcc -O3 -mavx2 -mbmi2 -mpopcnt
 * compilation of the C intrinsics version (see rej_uniform_eta4_avx2.c).
 *
 * Signature: unsigned mld_rej_uniform_eta4_avx2_asm(int32_t *r,
 *                                                  const uint8_t *buf,
 *                                                  const uint8_t *table)
 *   rdi = r (output)
 *   rsi = buf (input, 272 bytes)
 *   rdx = table (= mld_rej_uniform_table, 256x8 bytes)
 *
 * The C intrinsics version doesn't take the table — it uses a global. Our asm
 * wrapper takes table as 3rd arg for HOL-Light proof contract clarity. We
 * shadow it to %rsi (matching gcc convention) and re-load buf via %r9/%r10.
 */

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLD_CONFIG_NO_KEYPAIR_API) &&       \
    !defined(MLD_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLD_CONFIG_MULTILEVEL_WITH_SHARED) || MLDSA_ETA == 4)
/* simpasm: header-end */

        .text
        .balign 16
        .global MLD_ASM_NAMESPACE(rej_uniform_eta4_avx2_asm)
MLD_ASM_FN_SYMBOL(rej_uniform_eta4_avx2_asm)

        endbr64
        // Args: rdi=r, rsi=buf, rdx=table
        // We rearrange to match the gcc-compiled C intrinsics convention:
        //   r10 = original buf base (used by scalar tail offset calc)
        //   r9  = current buf+pos pointer (used by SIMD vpmovzxbw)
        //   rsi = table base (was global in C, passed in rdx)
        //   r8d = pos (offset from buf)
        //   eax = ctr (output count)
        movq    %rsi, %r10            // r10 = buf
        movq    %rsi, %r9             // r9 = buf
        movq    %rdx, %rsi            // rsi = table (was loaded via lea in C)
        xorl    %r8d, %r8d            // pos = 0
        xorl    %eax, %eax            // ctr = 0
        movabsq $1085102592571150095, %rdx   // 0x0F0F0F0F0F0F0F0F
        vmovq   %rdx, %xmm4
        movl    $4, %edx
        vmovd   %edx, %xmm3
        movl    $-9, %edx
        vpbroadcastq %xmm4, %ymm4              // ymm4 = mask 0x0F broadcast
        vmovd   %edx, %xmm2
        vpbroadcastb %xmm3, %ymm3              // ymm3 = eta=4 broadcast
        vpbroadcastb %xmm2, %ymm2              // ymm2 = -bound=-9 broadcast
        jmp     .L9_asm
        .p2align 4,,10
        .p2align 3
.L2_asm:
        movzbl  %cl, %r11d
        vpsrldq $8, %xmm0, %xmm1
        vmovq   (%rsi,%r11,8), %xmm5
        movq    %r11, %rcx
        movl    %eax, %r11d
        popcntl %ecx, %ecx
        addl    %ecx, %eax
        movl    %edx, %ecx
        vpshufb %xmm5, %xmm1, %xmm1
        shrl    $16, %ecx
        vpmovsxbd %xmm1, %ymm1
        vmovdqu %ymm1, (%rdi,%r11,4)
        cmpl    $248, %eax
        ja      .L33_asm
        movzbl  %cl, %r11d
        vextracti128 $0x1, %ymm0, %xmm0
        shrl    $24, %edx
        vmovq   (%rsi,%r11,8), %xmm1
        movq    %r11, %rcx
        movl    %eax, %r11d
        popcntl %ecx, %ecx
        addl    %ecx, %eax
        vpshufb %xmm1, %xmm0, %xmm1
        vpmovsxbd %xmm1, %ymm1
        vmovdqu %ymm1, (%rdi,%r11,4)
        cmpl    $248, %eax
        ja      .L34_asm
        movl    %edx, %ecx
        vpsrldq $8, %xmm0, %xmm0
        popcntl %edx, %edx
        addl    $16, %r8d
        vmovq   (%rsi,%rcx,8), %xmm1
        movl    %eax, %ecx
        addl    %edx, %eax
        addq    $16, %r9
        vpshufb %xmm1, %xmm0, %xmm0
        vpmovsxbd %xmm0, %ymm0
        vmovdqu %ymm0, (%rdi,%rcx,4)
        cmpl    $248, %eax
        ja      .L3_asm
        cmpl    $256, %r8d
        ja      .L3_asm
.L9_asm:
        vpmovzxbw (%r9), %ymm1
        vpsllw  $4, %ymm1, %ymm0
        vpor    %ymm0, %ymm1, %ymm1
        vpand   %ymm4, %ymm1, %ymm1
        vpsubb  %ymm1, %ymm3, %ymm0
        vpaddb  %ymm1, %ymm2, %ymm1
        vpmovmskb %ymm1, %edx
        movzbl  %dl, %r11d
        movzbl  %dl, %ecx
        vmovq   (%rsi,%r11,8), %xmm5
        popcntl %ecx, %ecx
        movl    %eax, %r11d
        addl    %ecx, %eax
        movl    %edx, %ecx
        vpshufb %xmm5, %xmm0, %xmm5
        shrl    $8, %ecx
        vpmovsxbd %xmm5, %ymm5
        vmovdqu %ymm5, (%rdi,%r11,4)
        cmpl    $248, %eax
        jbe     .L2_asm
        addl    $4, %r8d
.L3_asm:
        cmpl    $255, %eax
        ja      .L1_asm
        cmpl    $271, %r8d
        ja      .L1_asm
        movl    %r8d, %ecx
        addl    $1, %r8d
        movl    $4, %r9d
        addq    %r10, %rcx
        subl    %ecx, %r8d
        .p2align 4,,10
        .p2align 3
.L14_asm:
        movzbl  (%rcx), %edx
        movl    %edx, %esi
        shrb    $4, %dl
        andl    $15, %esi
        movzbl  %dl, %edx
        cmpb    $8, %sil
        ja      .L11_asm
        movzbl  %sil, %esi
        movl    %r9d, %r11d
        movl    %eax, %r10d
        addl    $1, %eax
        subl    %esi, %r11d
        movl    %r11d, (%rdi,%r10,4)
.L11_asm:
        cmpl    $255, %eax
        setbe   %sil
        cmpl    $8, %edx
        ja      .L12_asm
        testb   %sil, %sil
        je      .L12_asm
        movl    %r9d, %r10d
        leal    1(%rax), %esi
        subl    %edx, %r10d
        movl    %r10d, (%rdi,%rax,4)
        leal    (%r8,%rcx), %eax
        cmpl    $271, %eax
        setbe   %dl
        cmpl    $255, %esi
        setbe   %al
        addq    $1, %rcx
        testb   %al, %dl
        je      .L35_asm
        movl    %esi, %eax
        jmp     .L14_asm
        .p2align 4,,10
        .p2align 3
.L12_asm:
        leal    (%r8,%rcx), %edx
        cmpl    $271, %edx
        setbe   %dl
        addq    $1, %rcx
        testb   %sil, %dl
        jne     .L14_asm
.L1_asm:
        vzeroupper
        ret
        .p2align 4,,10
        .p2align 3
.L35_asm:
        movl    %esi, %eax
        vzeroupper
        ret
        .p2align 4,,10
        .p2align 3
.L33_asm:
        addl    $8, %r8d
        jmp     .L3_asm
        .p2align 4,,10
        .p2align 3
.L34_asm:
        addl    $12, %r8d
        jmp     .L3_asm

/* simpasm: footer-start */
#endif /* MLD_ARITH_BACKEND_X86_64_DEFAULT && !MLD_CONFIG_NO_KEYPAIR_API && \
          !MLD_CONFIG_MULTILEVEL_NO_SHARED &&                               \
          (MLD_CONFIG_MULTILEVEL_WITH_SHARED || MLDSA_ETA == 4) */
