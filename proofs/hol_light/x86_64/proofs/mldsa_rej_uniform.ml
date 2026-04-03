(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Rejection uniform sampling (AVX2).                                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mldsa_specs.ml";;
needs "x86_64/proofs/mldsa_rej_uniform_table.ml";;

(*** print_literal_from_elf "x86_64/mldsa/mldsa_rej_uniform.o";;
 ***)

let mldsa_rej_uniform_mc = define_assert_from_elf
  "mldsa_rej_uniform_mc" "x86_64/mldsa/mldsa_rej_uniform.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;                                (* endbr64 *)
  0x49; 0xba; 0x00; 0x01; 0x02; 0xff; 0x03;              (* movabs $0xff050403ff020100,%r10 *)
  0x04; 0x05; 0xff;
  0xc4; 0xc1; 0xf9; 0x6e; 0xc2;                          (* vmovq  %r10,%xmm0 *)
  0x49; 0xba; 0x06; 0x07; 0x08; 0xff; 0x09;              (* movabs $0xff0b0a09ff080706,%r10 *)
  0x0a; 0x0b; 0xff;
  0xc4; 0xc3; 0xf9; 0x22; 0xc2; 0x01;                    (* vpinsrq $0x1,%r10,%xmm0,%xmm0 *)
  0x49; 0xba; 0x04; 0x05; 0x06; 0xff; 0x07;              (* movabs $0xff090807ff060504,%r10 *)
  0x08; 0x09; 0xff;
  0xc4; 0xc1; 0xf9; 0x6e; 0xda;                          (* vmovq  %r10,%xmm3 *)
  0x49; 0xba; 0x0a; 0x0b; 0x0c; 0xff; 0x0d;              (* movabs $0xff0f0e0dff0c0b0a,%r10 *)
  0x0e; 0x0f; 0xff;
  0xc4; 0xc3; 0xe1; 0x22; 0xda; 0x01;                    (* vpinsrq $0x1,%r10,%xmm3,%xmm3 *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc3; 0x01;                    (* vinserti128 $0x1,%xmm3,%ymm0,%ymm0 *)
  0x41; 0xb8; 0xff; 0xff; 0x7f; 0x00;                    (* mov    $0x7fffff,%r8d *)
  0xc4; 0xc1; 0x79; 0x6e; 0xc8;                          (* vmovd  %r8d,%xmm1 *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;                          (* vpbroadcastd %xmm1,%ymm1 *)
  0x41; 0xb8; 0x01; 0xe0; 0x7f; 0x00;                    (* mov    $0x7fe001,%r8d *)
  0xc4; 0xc1; 0x79; 0x6e; 0xd0;                          (* vmovd  %r8d,%xmm2 *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;                          (* vpbroadcastd %xmm2,%ymm2 *)
  0x31; 0xc0;                                            (* xor    %eax,%eax *)
  0x31; 0xc9;                                            (* xor    %ecx,%ecx *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;                          (* cmp    $0xf8,%eax *)
  0x77; 0x46;                                            (* ja     0xb9 *)
  0x81; 0xf9; 0x28; 0x03; 0x00; 0x00;                    (* cmp    $0x328,%ecx *)
  0x77; 0x3e;                                            (* ja     0xb9 *)
  0xc5; 0xfe; 0x6f; 0x1c; 0x0e;                          (* vmovdqu (%rsi,%rcx,1),%ymm3 *)
  0x83; 0xc1; 0x18;                                      (* add    $0x18,%ecx *)
  0xc4; 0xe3; 0xfd; 0x00; 0xdb; 0x94;                    (* vpermq $0x94,%ymm3,%ymm3 *)
  0xc4; 0xe2; 0x65; 0x00; 0xd8;                          (* vpshufb %ymm0,%ymm3,%ymm3 *)
  0xc5; 0xe5; 0xdb; 0xd9;                                (* vpand  %ymm1,%ymm3,%ymm3 *)
  0xc5; 0xe5; 0xfa; 0xe2;                                (* vpsubd %ymm2,%ymm3,%ymm4 *)
  0xc5; 0x7c; 0x50; 0xc4;                                (* vmovmskps %ymm4,%r8d *)
  0xf3; 0x45; 0x0f; 0xb8; 0xc8;                          (* popcnt %r8d,%r9d *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x24; 0xc2;                    (* vmovq  (%rdx,%r8,8),%xmm4 *)
  0xc4; 0xe2; 0x7d; 0x31; 0xe4;                          (* vpmovzxbd %xmm4,%ymm4 *)
  0xc4; 0xe2; 0x5d; 0x36; 0xdb;                          (* vpermd %ymm3,%ymm4,%ymm3 *)
  0xc5; 0xfe; 0x7f; 0x1c; 0x87;                          (* vmovdqu %ymm3,(%rdi,%rax,4) *)
  0x44; 0x01; 0xc8;                                      (* add    %r9d,%eax *)
  0xeb; 0xb3;                                            (* jmp    0x6c *)
  0x3d; 0x00; 0x01; 0x00; 0x00;                          (* cmp    $0x100,%eax *)
  0x73; 0x36;                                            (* jae    0xf6 *)
  0x81; 0xf9; 0x45; 0x03; 0x00; 0x00;                    (* cmp    $0x345,%ecx *)
  0x77; 0x2e;                                            (* ja     0xf6 *)
  0x44; 0x0f; 0xb7; 0x04; 0x0e;                          (* movzwl (%rsi,%rcx,1),%r8d *)
  0x44; 0x0f; 0xb6; 0x4c; 0x0e; 0x02;                    (* movzbl 0x2(%rsi,%rcx,1),%r9d *)
  0x41; 0xc1; 0xe1; 0x10;                                (* shl    $0x10,%r9d *)
  0x45; 0x09; 0xc8;                                      (* or     %r9d,%r8d *)
  0x41; 0x81; 0xe0; 0xff; 0xff; 0x7f; 0x00;              (* and    $0x7fffff,%r8d *)
  0x83; 0xc1; 0x03;                                      (* add    $0x3,%ecx *)
  0x41; 0x81; 0xf8; 0x01; 0xe0; 0x7f; 0x00;              (* cmp    $0x7fe001,%r8d *)
  0x73; 0xcc;                                            (* jae    0xb9 *)
  0x44; 0x89; 0x04; 0x87;                                (* mov    %r8d,(%rdi,%rax,4) *)
  0x83; 0xc0; 0x01;                                      (* add    $0x1,%eax *)
  0xeb; 0xc3;                                            (* jmp    0xb9 *)
  0xc5; 0xf8; 0x77;                                      (* vzeroupper *)
  0xc3                                                   (* ret *)
];;
(*** BYTECODE END ***)

let mldsa_rej_uniform_tmc =
  define_trimmed "mldsa_rej_uniform_tmc" mldsa_rej_uniform_mc;;

let MLDSA_REJ_UNIFORM_EXEC = X86_MK_CORE_EXEC_RULE mldsa_rej_uniform_tmc;;

(* ------------------------------------------------------------------------- *)
(* An abbreviation used within the proof, though expanded in the spec.       *)
(* For ML-DSA, we extract 23-bit values from 3-byte windows and accept       *)
(* those < MLDSA_Q = 8380417.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REJ_SAMPLE = define
 `MLDSA_REJ_SAMPLE l = FILTER (\x. val x < 8380417) (MAP (word_zx:23 word->int32) l)`;;

let MLDSA_REJ_SAMPLE_EMPTY = prove
 (`MLDSA_REJ_SAMPLE [] = []`,
  REWRITE_TAC[MLDSA_REJ_SAMPLE; FILTER; MAP]);;

let MLDSA_REJ_SAMPLE_APPEND = prove
 (`!l1 l2. MLDSA_REJ_SAMPLE(APPEND l1 l2) =
           APPEND (MLDSA_REJ_SAMPLE l1) (MLDSA_REJ_SAMPLE l2)`,
  REWRITE_TAC[MLDSA_REJ_SAMPLE; MAP_APPEND; FILTER_APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Specification: to be completed with full Hoare triple.                    *)
(* The function takes:                                                       *)
(*   rdi = output buffer r (256 x int32)                                     *)
(*   rsi = input buffer buf (840 bytes)                                      *)
(*   rdx = lookup table (256 x 8 bytes)                                      *)
(* Returns in eax: number of valid coefficients (at most 256)                *)
(* Each output coefficient satisfies 0 <= c < 8380417                        *)
(* ------------------------------------------------------------------------- *)

(* Proof to be completed. *)
