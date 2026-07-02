(* Sub-iter-2 store-fold pieces (validated 2026-06-18, post session-rebuild). All the gather-side
   ingredients work; the OPEN issue is fold-carry-forward across states (see memory note).
   Load AFTER: main file, cbb_defs, .pf_target_proof (SUBWORD_ZX_LOW/ZX_128_256_128/SUBWORD_USHR),
   .maskbit_tgt_2_tac, .tab2_teq_tac, and pf_target (from cbb_defs). *)

(* pf_target_2 : built by substituting g1->g2, mask8->mask8b, pshuf1->pshuf2 into pf_target. *)
let pf_target_2 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
  subst [g2,g1; `mask8b:int64`,`mask8:int64`; `pshuf2:int256`,`pshuf1:int256`] pf_target;;

(* PF_PROOF_2 : discharges `pshuf2 = pf_target_2` (genuine table bridge for sub-iter 2). *)
let PF_PROOF_2 : tactic =
  W(fun (asl,w) ->
    let pdef = find (fun th -> is_eq(concl th) && rand(concl th)=`pshuf2:int256` && can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
    let teq0 = find (fun th -> is_eq(concl th) &&
        (lhand(concl th)=`tab2:int256` || rand(concl th)=`tab2:int256`) &&
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th) &&
        not(can(find_term(fun u->u=`f1bnd:int256`))(concl th))) (map snd asl) in
    let teq = if lhand(concl teq0)=`tab2:int256` then teq0 else SYM teq0 in
    SUBST1_TAC(SYM pdef) THEN REWRITE_TAC[teq] THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ZX_TRIVIAL; VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV SUBWORD_ZX_LOW_CONV) THEN REWRITE_TAC[ZX_128_256_128]);;

(* SI2_GATHER_TO_STORE : from post-SI1 s23 -> s29 store in usimd8 form + mask8b/tab2/maskbit_tgt_2 live.
   (Steps: REABBREV mask8b, maskbit_tgt_2, gather s24-28 with teq2, ABBREV acc1, store s29, sx2 usimd8.) *)
let SI2_GATHER_TO_STORE : tactic =
  REABBREV_TAC `mask8b = read R8 s23` THEN
  (SUBGOAL_THEN maskbit_tgt_2 ASSUME_TAC THENL [MASKBIT_TGT_2_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (24--24) THEN
  X86_VERBOSE_STEP_TAC EXEC "s25" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s24 = mask8b:int64`]) THEN
  X86_VSTEPS_TAC EXEC (26--26) THEN TAB2_TEQ_TAC THEN REABBREV_TAC `tab2 = read YMM6 s26` THEN
  X86_VSTEPS_TAC EXEC (27--27) THEN REABBREV_TAC `pshuf2 = read YMM6 s27` THEN
  PURGE_STALE_STATES_TAC ["s26"] THEN
  X86_VSTEPS_TAC EXEC (28--28) THEN REABBREV_TAC `sx2 = read YMM1 s28` THEN
  ABBREV_TAC `acc1 = outlen0 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` THEN
  VAL_INT64_TAC `acc1:num` THEN
  X86_STEPS_TAC EXEC (29--29) THEN
  SUBGOAL_THEN `sx2:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf2:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx2def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx2:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx2def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC];;
