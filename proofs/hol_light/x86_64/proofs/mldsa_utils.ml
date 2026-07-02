(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* Some convenient proof tools.                                              *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let MEMORY_128_FROM_16_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(16*i) in
      READ_MEMORY_MERGE_CONV 3 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

(* This tactic repeated calls `f n with monotonically increasing values of n
   until the target PC matches one of the assumptions.

   The goal must be of the form `ensure arm ...`. Clauses constraining the PC
   must be of the form `read PC some_state = some_value`. *)
let MAP_UNTIL_TARGET_PC f n = fun (asl, w) ->
  let is_pc_condition = can (term_match [] `read PC some_state = some_value`) in
  (* We assume that the goal has the form
     `ensure arm (\s. ... /\ read PC s = some_value /\ ...)` *)
  let extract_target_pc_from_goal goal =
    let _, insts, _ = term_match [] `eventually x86 (\s'. P) some_state` goal in
    insts
      |> rev_assoc `P: bool`
      |> conjuncts
      |> find is_pc_condition in
  (* Find PC-constraining assumption from the list of all assumptions. *)
  let extract_pc_assumption asl =
    try Some (find (is_pc_condition o concl o snd) asl |> snd |> concl) with find -> None in
  (* Check if there is an assumption constraining the PC to the target PC *)
  let has_matching_pc_assumption asl target_pc =
    match extract_pc_assumption asl with
     | None -> false
     | Some(asm) -> can (term_match [`returnaddress: 64 word`; `pc: num`] target_pc) asm in
  let target_pc = extract_target_pc_from_goal w in
  (* ALL_TAC if we reached the target PC, NO_TAC otherwise, so
     TARGET_PC_REACHED_TAC target_pc ORELSE SOME_OTHER_TACTIC
     is effectively `if !(target_pc_reached) SOME_OTHER_TACTIC` *)
  let TARGET_PC_REACHED_TAC target_pc = fun (asl, w) ->
    if has_matching_pc_assumption asl target_pc then
      ALL_TAC (asl, w)
    else
      NO_TAC (asl, w) in
  let rec core n (asl, w) =
    (TARGET_PC_REACHED_TAC target_pc ORELSE (f n THEN core (n + 1))) (asl, w)
  in
    core n (asl, w);;

(* ------------------------------------------------------------------------- *)
(* Byte->nibble decomposition helpers, shared between the eta2/eta4          *)
(* rejection-sampling proofs.                                                *)
(*                                                                           *)
(* NB: these are byte-for-byte identical to the definitions in              *)
(* aarch64/proofs/aarch64_utils.ml (merged in #176-era AArch64 eta work).   *)
(* They are duplicated here so the x86 proofs do not depend on the AArch64  *)
(* utils file; at upstream-PR time the intent is to hoist the shared set    *)
(* into common/mldsa_specs.ml and drop both copies.                         *)
(* ------------------------------------------------------------------------- *)

(* Internal byte->nibble decomposition stored in int16 lanes (matching the   *)
(* SIMD register layout used by the loop body). The public spec uses        *)
(* BYTES_TO_NIBBLES at the natural 4-word bitwidth instead; this view is    *)
(* bridged to the public one via NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES.       *)
let NIBBLE_PAIR = define
  `NIBBLE_PAIR (b:byte) =
   [word(val b MOD 16):int16; word(val b DIV 16):int16]`;;

let NIBBLES_OF_BYTES = define
  `NIBBLES_OF_BYTES [] = ([]:(int16)list) /\
   NIBBLES_OF_BYTES (CONS (b:byte) t) =
   APPEND (NIBBLE_PAIR b) (NIBBLES_OF_BYTES t)`;;

let NIBBLES_OF_BYTES_APPEND = prove
 (`!l1 l2. NIBBLES_OF_BYTES(APPEND l1 l2) =
           APPEND (NIBBLES_OF_BYTES l1) (NIBBLES_OF_BYTES l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; APPEND; APPEND_ASSOC]);;

(* Splits each input byte into its low and high 4-bit nibbles, expressed at *)
(* the natural 4-bit width consumed by the REJ_SAMPLE_ETA{2,4} spec. The    *)
(* output is twice the length of the input. Used at the proof boundary to   *)
(* bridge the byte-shaped internal proof view to the nibble-shaped public   *)
(* spec.                                                                    *)
let BYTES_TO_NIBBLES = define
  `BYTES_TO_NIBBLES [] = ([]:(4 word) list) /\
   BYTES_TO_NIBBLES (CONS (b:byte) t) =
   APPEND [word(val b MOD 16):4 word; word(val b DIV 16):4 word]
          (BYTES_TO_NIBBLES t)`;;
