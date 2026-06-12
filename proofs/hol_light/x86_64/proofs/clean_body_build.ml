(* ============================================================================
   CLEAN_BODY full proof build (2026-06-12). Run via loadt AFTER the main file
   is loaded (it uses EXEC, the store lemmas, SUBITER_STORE_SPEC, etc.).
   Non-interactive: either proves MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY or fails at
   the first bad tactic. Assembled from the validated interactive session.
   ============================================================================ *)

let EXEC = MLDSA_REJ_UNIFORM_ETA4_EXEC;;

let PURGE_STALE_STATES_TAC names =
  let rec refs_stale tm = match tm with
    | Comb(Comb(Const("read",_),_),Var(nm,_)) when List.mem nm names -> true
    | Comb(a,b) -> refs_stale a || refs_stale b | Abs(_,b) -> refs_stale b | _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th -> if refs_stale (concl th) then ALL_TAC else failwith "keep"));;

let OP8_R8B_READ = prove
 (`!s:x86state. read (OPERAND8 (% r8b) s) s = word(val(read R8 s) MOD 256)`,
  GEN_TAC THEN REWRITE_TAC[OPERAND8; r8b; GPR8; register_size; regsize] THEN
  REWRITE_TAC[GSYM(NUM_EXP_CONV `2 EXP 8`)] THEN
  ONCE_REWRITE_TAC[MESON[EXP; DIV_1] `x MOD 2 EXP n = x DIV 2 EXP 0 MOD 2 EXP n`] THEN
  REWRITE_TAC[GSYM word_subword; READ_COMPONENT_COMPOSE; R8] THEN
  REWRITE_TAC[bottom_32; bottom_16; bottom_8; bottomhalf; READ_SUBWORD] THEN
  ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN REWRITE_TAC[BIT_WORD_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let MOVZBL_R10_CAPTURE_TAC : tactic =
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[OP8_R8B_READ] THENC ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV));;

let DROP_WORDJOIN_TAC : tactic = fun (asl,w) ->
  (REPEAT(FIRST_X_ASSUM(fun th ->
     if can (find_term (fun u -> match u with Const("word_join",_) -> true | _ -> false)) (concl th)
     then ALL_TAC else failwith "keep"))) (asl,w);;

let wzx_id = prove(`!x:int128. word_zx x:int128 = x`, REWRITE_TAC[WORD_ZX_TRIVIAL]);;
let exp8 = prove(`(256:num) = 2 EXP 8`, CONV_TAC NUM_REDUCE_CONV);;

let IDX_RED_ETA4 = prove
 (`val (word_zx (word_zx (word (val (mask8:int64) MOD 256):byte):int32):int64) = val mask8 MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD] THEN SIMP_TAC[DIMINDEX_64;DIMINDEX_32;DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SUBGOAL_THEN `val (mask8:int64) MOD 256 < 256` ASSUME_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 256 /\ n < 4294967296 /\ n < 18446744073709551616`]]);;

Printf.printf "CLEAN_BODY_BUILD: helpers defined\n";;
