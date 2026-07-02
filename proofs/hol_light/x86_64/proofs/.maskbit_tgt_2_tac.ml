(* maskbit_tgt_2 + MASKBIT_TGT_2_TAC: sub-iter-2 analog of maskbit_tgt/MASKBIT_TGT_TAC.
   mask8b = R8 after the ushr-by-8 (= bits 8-15 of SUM32). maskbit_tgt_2 relates
   bit j (word(val mask8b MOD 256)) to chunk0 nibbles 32,40,48,56 (lanes 8-15) < 9.
   KEY EXTRA vs si1: val mask8b MOD 256 = (SUM32 DIV 256) MOD 256 (MASK_SHIFT8_MOD256);
   regroup SUM32 = SUM_low8 + 256*SUM8' + 65536*SUM_high16 (ARITH, linear in bitvals);
   DIVMOD256_SPLIT extracts SUM8' (= the lanes-8-15 8-term bitsum). Then same MASK_LOW_BIT
   + lanes-8-15 maskbit forall mechanism as si1. valeq MUST be folded via REWRITE_RULE[m8b]
   so its LHS is `val mask8b MOD 256` (not the unfolded word_zx tower). *)
let DIVMOD256_SPLIT = prove
 (`!a b c. a < 256 /\ b < 256 ==> (a + 256 * b + 65536 * c) DIV 256 MOD 256 = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 256 * b + 65536 * c) DIV 256 = b + 256 * c` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `b + 256 * c = c * 256 + b`; MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT]]);;

let maskbit_tgt_2 =
  `!j. j < 8 ==> (bit j (word (val (mask8b:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (32,8):byte) MOD 16;
         val(word_subword chunk0 (32,8):byte) DIV 16; val(word_subword chunk0 (40,8):byte) MOD 16;
         val(word_subword chunk0 (40,8):byte) DIV 16; val(word_subword chunk0 (48,8):byte) MOD 16;
         val(word_subword chunk0 (48,8):byte) DIV 16; val(word_subword chunk0 (56,8):byte) MOD 16;
         val(word_subword chunk0 (56,8):byte) DIV 16] < 9)`;;

let MASKBIT_TGT_2_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8b = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let sum_low8 = mksum [0;1;2;3;4;5;6;7] [1;2;4;8;16;32;64;128] in
    let sum8' = mksum [8;9;10;11;12;13;14;15] [1;2;4;8;16;32;64;128] in
    let sum_high16 = mksum (16--31) (map (fun i->1 lsl (i-16)) (16--31)) in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` sum_low8
       (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `256` sum8')
                                      (mk_binop `( * ):num->num->num` `65536` sum_high16))), ARITH_TAC) in
    let low8lt = prove(mk_binop `(<):num->num->bool` sum_low8 `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--7)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (8--15)))) THEN ARITH_TAC) in
    let vshift = SPEC sum32 MASK_SHIFT8_MOD256 in
    let dms = MP (SPECL [sum_low8; sum8'; sum_high16] DIVMOD256_SPLIT) (CONJ low8lt s8lt) in
    let valeq = REWRITE_RULE[m8b] (TRANS vshift (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `256`)) `256`) dms)) in
    let beq = mk_eq(`word (val (mask8b:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (8--15) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb2 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c) &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb2 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8b:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;
