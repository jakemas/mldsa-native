(* ========================================================================= *)
(* DEV SCRATCH — sound CLEAN_BODY lemma replacing the UNSOUND BODY_CHEAT.     *)
(*                                                                           *)
(* NOT loaded by the main proof. This is the work-in-progress tactic for the *)
(* clean (non-mid-exiting) loop body iteration i -> i+1, valid for i+1 < N.  *)
(*                                                                           *)
(* WHY BODY_CHEAT IS UNSOUND: the asm has mid-iter `ja $248` exits after     *)
(* sub-iters 1,2,3. BODY_CHEAT claims RCX=16(i+1) on the i=N-1 -> pc2 path,  *)
(* but the final iteration can mid-exit with a PARTIAL RCX=16(N-1)+4k. For   *)
(* i+1 < N, NIBLEN_PREFIX_MONO + CLEAN_BLOCK_BOUNDS guarantee niblen at      *)
(* 16i, 16i+4, 16i+8, 16i+12 are all <= 248, so NO mid-exit fires: the       *)
(* iteration is clean and RCX=16(i+1) genuinely holds. CLEAN_BODY proves     *)
(* exactly that. The messy partial final iteration is absorbed by            *)
(* FINAL_BLOCK (pc+56 with loopinv(N-1) -> function return pc+406), so the   *)
(* partial state is never exposed at the loop-exit pc+318.                   *)
(* ========================================================================= *)

(* ---- VALIDATED PROLOGUE (interactively confirmed lands pc+110, s11) ----  *)
(* After MAP_EVERY X_GEN_TAC + the CLEAN_BODY hypotheses stripped:           *)
(*
  ABBREV_TAC `outlist0 = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist):int32 list` THEN
  ABBREV_TAC `outlen0 = LENGTH(outlist0:int32 list)` THEN
  SUBGOAL_THEN `outlen0 <= 248` ASSUME_TAC THENL
   [EXPAND_TAC "outlen0" THEN EXPAND_TAC "outlist0" THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    TRANS_TAC LE_TRANS
     `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i+1)) inlist):int16 list)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(outlist0:int32 list) = outlen0`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
     can (find_term (fun t -> t = `RAX`)) (concl th) && is_conj(concl th))) THEN
  SUBGOAL_THEN `16 * i <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i + 1) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`buf:int64`;`272`;`inlist:byte list`;`i:num`;`s0:x86state`]
    SUB_LIST_16_BYTES_FROM_INT128) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i+1) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf (word(16*i)))) s0` THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(LAND_CONV NUM_REDUCE_CONV THENC REWRITE_CONV[]))) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN   (* -> pc+79, head guards passed *)
*)

(* ---- VALIDATED SIMD-SETUP STEPPING (per-op, no goal blowup) ----          *)
(* PURGE_STALE_STATES_TAC (define at top of dev session):
  let PURGE_STALE_STATES_TAC names =
    let refs_stale tm =
      let rec go t = match t with
        | Comb(Comb(Const("read",_),_),Var(nm,_)) when List.mem nm names -> true
        | Comb(a,b) -> go a || go b
        | Abs(_,b) -> go b
        | _ -> false in go tm in
    REPEAT(FIRST_X_ASSUM(fun th ->
      if refs_stale (concl th) then ALL_TAC else failwith "keep"));;

   Pattern PER vector op n (writing YMMk): VSTEP one, fold prior abbrevs into
   the new value eq, REABBREV, purge prior state. Confirmed s5..s8:
  X86_VSTEPS_TAC EXEC (5--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[<chunk0 mem-eq>; ARITH_RULE `1 * x = x`]) THEN
  REABBREV_TAC `f0load = read YMM0 s5` THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = f0load`]) THEN
  REABBREV_TAC `f1shl = read YMM1 s6` THEN PURGE_STALE_STATES_TAC ["s5"] THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s6 = f0load`;
                              ASSUME `read YMM1 s6 = f1shl`]) THEN
  REABBREV_TAC `f0or = read YMM0 s7` THEN PURGE_STALE_STATES_TAC ["s6"] THEN
  X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s7 = f0or`]) THEN
  REABBREV_TAC `f0nib = read YMM0 s8` THEN PURGE_STALE_STATES_TAC ["s7"] THEN
  X86_VSTEPS_TAC EXEC (9--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s8 = f0nib`]) THEN
  REABBREV_TAC `f1bnd = read YMM1 s9` THEN PURGE_STALE_STATES_TAC ["s8"] THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s9 = f0nib`]) THEN
  REABBREV_TAC `f0sub = read YMM0 s10` THEN PURGE_STALE_STATES_TAC ["s9"] THEN
  X86_VSTEPS_TAC EXEC (11--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM1 s10 = f1bnd`]) THEN
  REABBREV_TAC `mask8 = read R8 s11` THEN PURGE_STALE_STATES_TAC ["s10"]
  (* ^ VALIDATED end-to-end: lands pc+110 (first vextracti128), ~46 assums,
     registers abbreviated: f0load,f1shl,f0or,f0nib,f1bnd,f0sub,mask8.
     f0sub holds the (4-nibble) byte vector; mask8 the popcount mask. *) *)

(* TODO next session:
   - For VALUE correctness (not just shape), replace opaque REABBREV of the
     nibble/sub vectors with SUBGOAL_THEN `read YMMk sN = word(num_of_wordlist
     <nibbles/4-minus-nibble list of chunk0 bytes>)` proven via the lane
     lemmas (VPMOVZXBW_LANE_EXTRACT, VPSLLW_VPOR_VPAND_*, VPSUBB_SIGN_BIT_LT_9).
   - Then per sub-iter k=0..3: extract g0 (vextracti128/vpsrldq), movzbl mask
     low byte -> table index, vmovq table[idx], vpshufb, vpmovsxbd, vmovdqu
     store. At the store apply GATHER_FILTER_MAP_IDX_8 + PSHUFB_ACCEPTED_PREFIX_NUM
     + VPMOVSXBD_LANE_EXTRACT + WORD_SUB_4_NIBBLE_INT32_AS_SX + ETA_GATHER to
     show stored bytes = REJ_SAMPLE_ETA4_BYTES of the 4-byte block.
   - popcnt add: RAX_BOUND_AFTER_POPCNT_ADD_DIRECT. mid guard: JA_NOT_TAKEN_LE
     with CLEAN_BLOCK_BOUNDS (clean iter, no exit). Compose 4 sub-iters via
     SUBITER_OUTLEN_STEP_4 + REJ_SAMPLE_ETA4_BYTES_16_AS_4 + _STEP_16.
   - jmp back to pc+56; ENSURES_FINAL_STATE_TAC; outlen=16(i+1) shape. *)
