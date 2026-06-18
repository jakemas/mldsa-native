(* Sub-iter-4 fold pieces. g4 = hi 128 lane >>64 = word_zx(word_zx(word_ushr(word_zx(word_zx(word_subword
   f0sub (128,128)))) 64)). mask8d (R8 ushr24), block3 = SUB_LIST(16i+12,4), lanes 24-31. BYTE3 (DIV 2^24).
   NO mid-guard (sub-iter 4 ends jmp pc+56). *)

let DIVMOD16777216_SPLIT = prove
 (`!a b. a < 16777216 ==> (a + 16777216 * b) DIV 16777216 MOD 256 = b MOD 256`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 16777216 * b) DIV 16777216 = b` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC);;

let R_EQ_D = prove(`val (word_zx (word_zx (word (val (mask8d:int64) MOD 256):byte):int32):int64):num = val (mask8d:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;
let RLT_D = prove(`val (mask8d:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

let maskbit_tgt_4 =
  `!j. j < 8 ==> (bit j (word (val (mask8d:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (96,8):byte) MOD 16;
         val(word_subword chunk0 (96,8):byte) DIV 16; val(word_subword chunk0 (104,8):byte) MOD 16;
         val(word_subword chunk0 (104,8):byte) DIV 16; val(word_subword chunk0 (112,8):byte) MOD 16;
         val(word_subword chunk0 (112,8):byte) DIV 16; val(word_subword chunk0 (120,8):byte) MOD 16;
         val(word_subword chunk0 (120,8):byte) DIV 16] < 9)`;;

let MASKBIT_TGT_4_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8d_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8d:int64` && can(find_term(fun u->u=`mask8c:int64`))(concl th)) asms in
    let m8c_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8c:int64` && can(find_term(fun u->u=`mask8b:int64`))(concl th)) asms in
    let m8b_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` && can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b_def) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let low24 = mksum (0--23) (map (fun i->1 lsl i) (0--23)) in
    let sum8''' = mksum [24;25;26;27;28;29;30;31] [1;2;4;8;16;32;64;128] in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` low24
       (mk_binop `( * ):num->num->num` `16777216` sum8''')), ARITH_TAC) in
    let low24lt = prove(mk_binop `(<):num->num->bool` low24 `16777216`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--23)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8''' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (24--31)))) THEN ARITH_TAC) in
    (* mask8d over SUM32: subst mask8c def (over mask8b) then mask8b def (over SUM32) *)
    let m8d_over_sum = REWRITE_RULE[SYM m8b_def] (REWRITE_RULE[SYM m8c_def] m8d_def) in
    let vshift = SPEC sum32 MASK_SHIFT24_MOD256 in
    let dms = MP (SPECL [low24; sum8'''] DIVMOD16777216_SPLIT) low24lt in
    let s8mod = prove(mk_eq(mk_binop `MOD` sum8''' `256`, sum8'''), MATCH_MP_TAC MOD_LT THEN ACCEPT_TAC s8lt) in
    let valeq = TRANS (REWRITE_RULE[m8d_over_sum] vshift)
                  (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `16777216`)) `256`) (TRANS dms s8mod)) in
    let beq = mk_eq(`word (val (mask8d:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8''')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (24--31) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb4 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (120,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb4 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8d:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let TAB4_TEQ_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let tblinv = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s49",_))),_) ->
         can(find_term(fun u->u=`mldsa_rej_uniform_table:byte list`)) (concl th) | _ -> false) asms in
    let tvr = MP (ISPECL[`table:int64`;`val (mask8d:int64) MOD 256`;`s49:x86state`] TABLE_VMOVQ_READ) (CONJ tblinv RLT_D) in
    let ymm6 = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("YMM6",_)),Var("s50",_))),_)->true|_->false) asms in
    ASSUME_TAC (REWRITE_RULE[R_EQ_D; tvr] ymm6));;

let pf_target_4 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
  subst [g4,g1; `mask8d:int64`,`mask8:int64`; `pshuf4:int256`,`pshuf1:int256`] pf_target;;

let PF_PROOF_4 : tactic =
  W(fun (asl,w) ->
    let pdef = find (fun th -> is_eq(concl th) && rand(concl th)=`pshuf4:int256` && can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
    let teq0 = find (fun th -> is_eq(concl th) &&
        (lhand(concl th)=`tab4:int256` || rand(concl th)=`tab4:int256`) &&
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th) &&
        not(can(find_term(fun u->u=`f1bnd:int256`))(concl th))) (map snd asl) in
    let teq = if lhand(concl teq0)=`tab4:int256` then teq0 else SYM teq0 in
    SUBST1_TAC(SYM pdef) THEN REWRITE_TAC[teq] THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ZX_TRIVIAL; VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV SUBWORD_ZX_LOW_CONV) THEN REWRITE_TAC[ZX_128_256_128]);;

(* ACC3_IDENT_TAC: LENGTH(REJ_SAMPLE(SUB_LIST(0,16i+12)))=acc3 by forward inference. acc3 = acc2 +
   niblen(SUB_LIST(16i+8,4)); needs acc2_ident + acc3 ABBREV def. *)
let ACC3_IDENT_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let acc2_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc2",_))->true|_->false) asms in
    let acc3_def = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_))->true|_->false) asms in
    let split = REWRITE_RULE[ADD_CLAUSES; ARITH_RULE `(16*i+8)+4 = 16*i+12`] (ISPECL[`inlist:byte list`;`16*i+8`;`4`;`0`] SUB_LIST_SPLIT) in
    let step1 = (REWRITE_CONV[LENGTH_REJ_SAMPLE_ETA4_BYTES] THENC ONCE_DEPTH_CONV(REWR_CONV split) THENC REWRITE_CONV[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND])
                  `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)` in
    let acc2_nib = REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA4_BYTES] acc2_ident in
    let final = TRANS step1 (TRANS (AP_THM (AP_TERM `(+):num->num->num` acc2_nib) `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+8,4) inlist):int16 list)`) acc3_def) in
    ASSUME_TAC final);;
