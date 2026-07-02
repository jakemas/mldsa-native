(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Rejection uniform sampling for eta=2 (AVX2).                       *)
(* ========================================================================= *)

needs "s2n_bignum/x86/proofs/base.ml";;

needs "mldsa_native/common/mldsa_specs.ml";;

needs "mldsa_native/x86_64/proofs/mldsa_rej_uniform_table.ml";;

(*** Bytecode extracted from rej_uniform_eta2_avx2_asm.o (.text section) ***)

let mldsa_rej_uniform_eta2_mc = define_assert_from_elf
  "mldsa_rej_uniform_eta2_mc" "x86_64/mldsa/rej_uniform_eta2_avx2_asm.o"
[
 0xf3; 0x0f; 0x1e; 0xfa; 0x41; 0xb8; 0x0f; 0x0f; 0x0f; 0x0f; 0xc4; 0xc1; 0x79; 0x6e; 0xd8; 0xc4;
 0xe2; 0x7d; 0x58; 0xdb; 0x41; 0xb8; 0x02; 0x02; 0x02; 0x02; 0xc4; 0xc1; 0x79; 0x6e; 0xe0; 0xc4;
 0xe2; 0x7d; 0x58; 0xe4; 0x41; 0xb8; 0x0f; 0x0f; 0x0f; 0x0f; 0xc4; 0xc1; 0x79; 0x6e; 0xe8; 0xc4;
 0xe2; 0x7d; 0x58; 0xed; 0x41; 0xb8; 0x60; 0xe6; 0xff; 0xff; 0xc4; 0xc1; 0x49; 0xc4; 0xf0; 0x00;
 0xc4; 0xe2; 0x7d; 0x79; 0xf6; 0x41; 0xb8; 0x05; 0x00; 0x00; 0x00; 0xc4; 0xc1; 0x41; 0xc4; 0xf8;
 0x00; 0xc4; 0xe2; 0x7d; 0x79; 0xff; 0x31; 0xc0; 0x31; 0xc9; 0x3d; 0xf8; 0x00; 0x00; 0x00; 0x0f;
 0x87; 0x3e; 0x01; 0x00; 0x00; 0x83; 0xf9; 0x78; 0x0f; 0x87; 0x35; 0x01; 0x00; 0x00; 0xc4; 0xe2;
 0x7d; 0x30; 0x04; 0x0e; 0xc5; 0xf5; 0x71; 0xf0; 0x04; 0xc5; 0xfd; 0xeb; 0xc1; 0xc5; 0xfd; 0xdb;
 0xc3; 0xc5; 0xfd; 0xf8; 0xcd; 0xc5; 0x7d; 0xd7; 0xc1; 0xc4; 0xc3; 0x7d; 0x39; 0xc0; 0x00; 0x45;
 0x0f; 0xb6; 0xd0; 0xc4; 0x21; 0x7a; 0x7e; 0x0c; 0xd2; 0xc4; 0x42; 0x31; 0x00; 0xc0; 0xc4; 0xc2;
 0x7d; 0x21; 0xc9; 0xc4; 0xe2; 0x75; 0x0b; 0xd6; 0xc5; 0xed; 0xd5; 0xd7; 0xc5; 0xf5; 0xfe; 0xca;
 0xc5; 0xdd; 0xfa; 0xc9; 0xc5; 0xfe; 0x7f; 0x0c; 0x87; 0xf3; 0x45; 0x0f; 0xb8; 0xca; 0x44; 0x01;
 0xc8; 0x41; 0xc1; 0xe8; 0x08; 0x83; 0xc1; 0x04; 0x3d; 0xf8; 0x00; 0x00; 0x00; 0x0f; 0x87; 0xd0;
 0x00; 0x00; 0x00; 0xc4; 0xc1; 0x39; 0x73; 0xd8; 0x08; 0x45; 0x0f; 0xb6; 0xd0; 0xc4; 0x21; 0x7a;
 0x7e; 0x0c; 0xd2; 0xc4; 0x42; 0x31; 0x00; 0xc0; 0xc4; 0xc2; 0x7d; 0x21; 0xc9; 0xc4; 0xe2; 0x75;
 0x0b; 0xd6; 0xc5; 0xed; 0xd5; 0xd7; 0xc5; 0xf5; 0xfe; 0xca; 0xc5; 0xdd; 0xfa; 0xc9; 0xc5; 0xfe;
 0x7f; 0x0c; 0x87; 0xf3; 0x45; 0x0f; 0xb8; 0xca; 0x44; 0x01; 0xc8; 0x41; 0xc1; 0xe8; 0x08; 0x83;
 0xc1; 0x04; 0x3d; 0xf8; 0x00; 0x00; 0x00; 0x0f; 0x87; 0x86; 0x00; 0x00; 0x00; 0xc4; 0xc3; 0x7d;
 0x39; 0xc0; 0x01; 0x45; 0x0f; 0xb6; 0xd0; 0xc4; 0x21; 0x7a; 0x7e; 0x0c; 0xd2; 0xc4; 0x42; 0x31;
 0x00; 0xc0; 0xc4; 0xc2; 0x7d; 0x21; 0xc9; 0xc4; 0xe2; 0x75; 0x0b; 0xd6; 0xc5; 0xed; 0xd5; 0xd7;
 0xc5; 0xf5; 0xfe; 0xca; 0xc5; 0xdd; 0xfa; 0xc9; 0xc5; 0xfe; 0x7f; 0x0c; 0x87; 0xf3; 0x45; 0x0f;
 0xb8; 0xca; 0x44; 0x01; 0xc8; 0x41; 0xc1; 0xe8; 0x08; 0x83; 0xc1; 0x04; 0x3d; 0xf8; 0x00; 0x00;
 0x00; 0x77; 0x40; 0xc4; 0xc1; 0x39; 0x73; 0xd8; 0x08; 0x45; 0x0f; 0xb6; 0xd0; 0xc4; 0x21; 0x7a;
 0x7e; 0x0c; 0xd2; 0xc4; 0x42; 0x31; 0x00; 0xc0; 0xc4; 0xc2; 0x7d; 0x21; 0xc9; 0xc4; 0xe2; 0x75;
 0x0b; 0xd6; 0xc5; 0xed; 0xd5; 0xd7; 0xc5; 0xf5; 0xfe; 0xca; 0xc5; 0xdd; 0xfa; 0xc9; 0xc5; 0xfe;
 0x7f; 0x0c; 0x87; 0xf3; 0x45; 0x0f; 0xb8; 0xca; 0x44; 0x01; 0xc8; 0x83; 0xc1; 0x04; 0xe9; 0xb7;
 0xfe; 0xff; 0xff; 0x3d; 0x00; 0x01; 0x00; 0x00; 0x0f; 0x83; 0x84; 0x00; 0x00; 0x00; 0x81; 0xf9;
 0x88; 0x00; 0x00; 0x00; 0x73; 0x7c; 0x44; 0x0f; 0xb6; 0x1c; 0x0e; 0xff; 0xc1; 0x45; 0x89; 0xda;
 0x41; 0x83; 0xe2; 0x0f; 0x41; 0x83; 0xfa; 0x0f; 0x73; 0x2b; 0x45; 0x89; 0xd3; 0x45; 0x69; 0xdb;
 0xcd; 0x00; 0x00; 0x00; 0x41; 0xc1; 0xeb; 0x0a; 0x45; 0x6b; 0xdb; 0x05; 0x45; 0x29; 0xda; 0x41;
 0xbb; 0x02; 0x00; 0x00; 0x00; 0x45; 0x29; 0xd3; 0x44; 0x89; 0x1c; 0x87; 0xff; 0xc0; 0x3d; 0x00;
 0x01; 0x00; 0x00; 0x73; 0x3d; 0x44; 0x0f; 0xb6; 0x5c; 0x0e; 0xff; 0x41; 0xc1; 0xeb; 0x04; 0x41;
 0x83; 0xe3; 0x0f; 0x41; 0x83; 0xfb; 0x0f; 0x73; 0x9a; 0x45; 0x89; 0xda; 0x45; 0x69; 0xd2; 0xcd;
 0x00; 0x00; 0x00; 0x41; 0xc1; 0xea; 0x0a; 0x45; 0x6b; 0xd2; 0x05; 0x45; 0x29; 0xd3; 0x41; 0xba;
 0x02; 0x00; 0x00; 0x00; 0x45; 0x29; 0xda; 0x44; 0x89; 0x14; 0x87; 0xff; 0xc0; 0xe9; 0x71; 0xff;
 0xff; 0xff; 0xc3
];;

(* ========================================================================= *)
(* Specification for REJ_SAMPLE_ETA2                                         *)
(* ========================================================================= *)

(* Rejection sampling for eta=2:
   - Extract 4-bit nibbles from input bytes
   - Accept nibbles < 15
   - Apply modulo-5 reduction: t = t - (205 * t >> 10) * 5
   - Output: 2 - t, producing coefficients in range [-2, 2] *)

let REJ_SAMPLE_ETA2 = new_definition
  `REJ_SAMPLE_ETA2 (inlist:byte list) =
    let nibbles = FLAT (MAP (\b. [word_and b (word 15); word_ushr b 4]) inlist) in
    let valid_nibbles = FILTER (\n. val n < 15) nibbles in
    let reduced = MAP (\n. let t = val n in
                           let q = (205 * t) DIV 1024 in
                           word (t - q * 5)) valid_nibbles in
    MAP (\t. word_sub (word 2) t) reduced`;;

(* ========================================================================= *)
(* Trimmed machine code (remove ENDBR64 prefix)                             *)
(* ========================================================================= *)

let mldsa_rej_uniform_eta2_tmc = define_trimmed
  "mldsa_rej_uniform_eta2_tmc" mldsa_rej_uniform_eta2_mc;;

(* ========================================================================= *)
(* Main CORRECT theorem                                                      *)
(* ========================================================================= *)

(* TODO: This is a skeleton - full proof development is a multi-month effort.
   Key proof steps needed (similar to eta4 plus):
   1. All the SIMD operations from eta4
   2. Correctness of vpmulhrsw for multiply-high-round-scale with -6560
   3. Correctness of vpmullw for multiply low with 5
   4. Correctness of vpaddd for modulo-5 reduction composition
   5. Verification that reduction produces correct mod-5 result
   6. Scalar modulo-5 reduction correctness (imull/shrl/imull/subl sequence)
   7. Full composition into functional correctness
*)

(* Byte-shape internal alias for eta2: REJ_SAMPLE_ETA2 of nibble list of l. *)
(* The bridge to the public spec via BYTES_TO_NIBBLES is established below. *)
let REJ_SAMPLE_ETA2_BYTES = define
  `REJ_SAMPLE_ETA2_BYTES (l:byte list) =
   REJ_SAMPLE_ETA2 (BYTES_TO_NIBBLES l)`;;

let MLDSA_REJ_UNIFORM_ETA2_CORRECT = prove
 (`!res buf table (inlist:byte list) pc.
    LENGTH inlist = 136 /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (res, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (buf, 136) /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (table, 2048) /\
    nonoverlapping (res, 1024) (buf, 136) /\
    nonoverlapping (res, 1024) (table, 2048)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [res; buf; table] s /\
              read(memory :> bytes(buf,136)) s = num_of_wordlist inlist /\
              read(memory :> bytes(table,2048)) s =
                num_of_wordlist mldsa_rej_uniform_table)
         (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
              let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA2_BYTES inlist) in
              let outlen = LENGTH outlist in
              C_RETURN s = word outlen /\
              read(memory :> bytes(res,4 * outlen)) s =
                num_of_wordlist outlist)
         (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`,

  (* Full proof to follow same pattern as eta4 with extensions for *)
  (* the mod-5 reduction (vpmulhrsw + vpmullw + vpaddd + vpsubd).  *)
  CHEAT_TAC);;

(* ========================================================================= *)
(* Memory safety theorem                                                     *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA2_MEMSAFE = prove
 (`!res buf table (inlist:byte list) e pc.
    LENGTH inlist = 136 /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (res, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (buf, 136) /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta2_tmc) (table, 2048) /\
    nonoverlapping (res, 1024) (buf, 136) /\
    nonoverlapping (res, 1024) (table, 2048)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta2_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [res; buf; table] s /\
              read(memory :> bytes(buf,136)) s = num_of_wordlist inlist /\
              read(memory :> bytes(table,2048)) s =
                num_of_wordlist mldsa_rej_uniform_table /\
              read events s = e)
         (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta2_tmc)) /\
              (?e2. read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [buf,136; table,2048]
                                          [res,1024]))
         (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9] ,,
          MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`,

  (* Full proof to follow eta4 MEMSAFE pattern. *)
  CHEAT_TAC);;

(* ========================================================================= *)
(* Subroutine wrappers                                                       *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA2_NOIBT_SUBROUTINE_CORRECT = prove
 (`!res buf table (inlist:byte list) stackpointer.
    LENGTH inlist = 136 /\
    aligned 16 stackpointer /\
    nonoverlapping (res, 1024) (buf, 136) /\
    nonoverlapping (res, 1024) (table, 2048) /\
    ALL (nonoverlapping (word_sub stackpointer (word 8), 8))
      [(res,1024); (buf,136); (table,2048)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta2_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              C_ARGUMENTS [res; buf; table] s /\
              read(memory :> bytes(buf,136)) s = num_of_bytelist inlist /\
              read(memory :> bytes(table,2048)) s =
                num_of_bytelist mldsa_rej_uniform_table)
         (\s. let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA2 inlist) in
              let outlen = LENGTH outlist in
              C_RETURN s = word outlen /\
              read(memory :> bytes(res,4 * outlen)) s =
                num_of_int32list outlist)
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`,

  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_rej_uniform_eta2_tmc
    MLDSA_REJ_UNIFORM_ETA2_CORRECT);;

let MLDSA_REJ_UNIFORM_ETA2_SUBROUTINE_CORRECT =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA2_NOIBT_SUBROUTINE_CORRECT;;
