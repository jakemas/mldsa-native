(* Sub-iter-3 fold pieces. g3 = hi 128 lane (no shift) = word_zx(word_zx(word_subword f0sub (128,128))).
   mask8c (R8 ushr16), block2 = SUB_LIST(16i+8,4), lanes 16-23. Load after main+cbb+pf_target_proof+
   si2_fold_complete (DIVMOD256_SPLIT, ACC1_IDENT_TAC) + .si3_full (SI3_PRE/MG/RESOLVE). *)

let DIVMOD65536_SPLIT = prove
 (`!a b c. a < 65536 /\ b < 256 ==> (a + 65536 * b + 16777216 * c) DIV 65536 MOD 256 = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 65536 * b + 16777216 * c) DIV 65536 = b + 256 * c` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `b + 256 * c = c * 256 + b`; MOD_MULT_ADD] THEN ASM_SIMP_TAC[MOD_LT]]);;

let R_EQ_C = prove(`val (word_zx (word_zx (word (val (mask8c:int64) MOD 256):byte):int32):int64):num = val (mask8c:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;
let RLT_C = prove(`val (mask8c:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

let maskbit_tgt_3 =
  `!j. j < 8 ==> (bit j (word (val (mask8c:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (64,8):byte) MOD 16;
         val(word_subword chunk0 (64,8):byte) DIV 16; val(word_subword chunk0 (72,8):byte) MOD 16;
         val(word_subword chunk0 (72,8):byte) DIV 16; val(word_subword chunk0 (80,8):byte) MOD 16;
         val(word_subword chunk0 (80,8):byte) DIV 16; val(word_subword chunk0 (88,8):byte) MOD 16;
         val(word_subword chunk0 (88,8):byte) DIV 16] < 9)`;;

let MASKBIT_TGT_3_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8c_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8c:int64` &&
        can(find_term(fun u->u=`mask8b:int64`))(concl th)) asms in
    let m8b_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b_def) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let low16 = mksum (0--15) (map (fun i->1 lsl i) (0--15)) in
    let sum8'' = mksum [16;17;18;19;20;21;22;23] [1;2;4;8;16;32;64;128] in
    let high8 = mksum (24--31) (map (fun i->1 lsl (i-24)) (24--31)) in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` low16
       (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `65536` sum8'')
                                      (mk_binop `( * ):num->num->num` `16777216` high8))), ARITH_TAC) in
    let low16lt = prove(mk_binop `(<):num->num->bool` low16 `65536`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--15)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8'' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (16--23)))) THEN ARITH_TAC) in
    let m8c_over_sum = REWRITE_RULE[SYM m8b_def] m8c_def in
    let vshift = SPEC sum32 MASK_SHIFT16_MOD256 in
    let dms = MP (SPECL [low16; sum8''; high8] DIVMOD65536_SPLIT) (CONJ low16lt s8lt) in
    let valeq = TRANS (REWRITE_RULE[m8c_over_sum] vshift) (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `65536`)) `256`) dms) in
    let beq = mk_eq(`word (val (mask8c:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8'')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (16--23) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb3 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c) &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (56,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb3 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8c:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let TAB3_TEQ_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let tblinv = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s37",_))),_) ->
         can(find_term(fun u->u=`mldsa_rej_uniform_table:byte list`)) (concl th) | _ -> false) asms in
    let tvr = MP (ISPECL[`table:int64`;`val (mask8c:int64) MOD 256`;`s37:x86state`] TABLE_VMOVQ_READ) (CONJ tblinv RLT_C) in
    let ymm6 = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("YMM6",_)),Var("s38",_))),_)->true|_->false) asms in
    ASSUME_TAC (REWRITE_RULE[R_EQ_C; tvr] ymm6));;

let pf_target_3 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
  subst [g3,g1; `mask8c:int64`,`mask8:int64`; `pshuf3:int256`,`pshuf1:int256`] pf_target;;

let PF_PROOF_3 : tactic =
  W(fun (asl,w) ->
    let pdef = find (fun th -> is_eq(concl th) && rand(concl th)=`pshuf3:int256` && can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
    let teq0 = find (fun th -> is_eq(concl th) &&
        (lhand(concl th)=`tab3:int256` || rand(concl th)=`tab3:int256`) &&
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th) &&
        not(can(find_term(fun u->u=`f1bnd:int256`))(concl th))) (map snd asl) in
    let teq = if lhand(concl teq0)=`tab3:int256` then teq0 else SYM teq0 in
    SUBST1_TAC(SYM pdef) THEN REWRITE_TAC[teq] THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ZX_TRIVIAL; VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV SUBWORD_ZX_LOW_CONV) THEN REWRITE_TAC[ZX_128_256_128]);;

(* ACC2_IDENT_TAC: prove & ASSUME LENGTH(REJ_SAMPLE(SUB_LIST(0,16i+8)))=acc2 by forward inference
   (non-destructive; needs acc1_ident [LENGTH REJ_SAMPLE form] + acc2 ABBREV def in asl). *)
let ACC2_IDENT_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let acc1_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc1",_))->true|_->false) asms in
    let acc2_def = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_))->true|_->false) asms in
    let split = REWRITE_RULE[ADD_CLAUSES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] (ISPECL[`inlist:byte list`;`16*i+4`;`4`;`0`] SUB_LIST_SPLIT) in
    let step1 = (REWRITE_CONV[LENGTH_REJ_SAMPLE_ETA4_BYTES] THENC ONCE_DEPTH_CONV(REWR_CONV split) THENC REWRITE_CONV[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND])
                  `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` in
    let acc1_nib = REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA4_BYTES] acc1_ident in
    let final = TRANS step1 (TRANS (AP_THM (AP_TERM `(+):num->num->num` acc1_nib) `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+4,4) inlist):int16 list)`) acc2_def) in
    ASSUME_TAC final);;
