(* MASKBIT_TGT_TAC: derive maskbit_tgt (the mask8-byte <-> chunk0-nibble<9 correspondence
   in EL-list form) IN-CONTEXT at ~s13. Uses the s13 mask8 def `word_zx(word(<32-bitsum>))=mask8`
   for the low-byte split (MASK_LOW_BIT mechanism, same as MASKBIT_PF_TAC step 1) and the
   pre-derived byte-0 maskbit forall (lanes 8*k <-> chunk0 nibbles 0,8,16,24) for step 2 --
   so it does NOT need f1bnd's word_join def (which is already dropped at s11). The 8 j-cases
   reduce to `P<=>P` via EL_CONV, closed by REFL_TAC. *)
let MASKBIT_TGT_TAC : tactic =
  W(fun (asl,w) ->
    let m8 = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) (map snd asl) in
    let sum32 = rand(rand(lhand(concl m8))) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let sum8 = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (List.map2 (fun wt bv -> if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) [1;2;4;8;16;32;64;128] (map (fun i->List.nth bvs i) (0--7))) in
    let high = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (map (fun i -> let wt = 1 lsl (i-8) in if wt=1 then List.nth bvs i else mk_binop `( * ):num->num->num` (mk_small_numeral wt) (List.nth bvs i)) (8--31)) in
    let splitth = prove(mk_eq(sum32, mk_binop `(+):num->num->num` sum8 (mk_binop `( * ):num->num->num` `256` high)), ARITH_TAC) in
    let byteeq32 = TRANS (AP_TERM `word:num->byte` splitth) (SPECL [sum8; high] WORD_ADD_256_BYTE) in
    let beq = mk_eq(`word (val (mask8:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8)) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (0--7) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb0 = find (fun th -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) (map snd asl) in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb0 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(`val (mask8:int64)`, mk_binop `MOD` sum32 `2 EXP 32`)) SUBST1_TAC THENL
       [SUBST1_TAC(SYM m8) THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
        MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [sum32; `2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_binop `MOD` (mk_binop `MOD` sum32 `2 EXP 32`) `256`, mk_binop `MOD` sum32 `256`)) SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV); ALL_TAC] THEN
      REWRITE_TAC[WORD_BYTE_MOD] THEN ACCEPT_TAC byteeq32;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;
