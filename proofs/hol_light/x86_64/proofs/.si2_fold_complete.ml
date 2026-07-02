(* Sub-iter-2 store fold COMPLETE + cheat-free (2026-06-18). The full generalized mechanism:
   gather (bg2 early) + maskbit_tgt_2 + teq2 + pf_target_2 + SUBITER_STORE_SPEC fold + carry-forward.
   KEY: the running prefix store must be stated with length = acc1 (the next write's offset var) so
   it carries past the s29 vpmovdqu write; acc1_ident bridges LENGTH(REJ_SAMPLE(SUB_LIST(0,16i+4)))=acc1.
   Load after main + cbb_defs + .pf_target_proof + .maskbit_tgt_2_tac + .tab2_teq_tac + .si2_fold_pieces. *)

(* LEN_RECONCILE_GEN: LEN_RECONCILE generalized to arbitrary 4 block bytes b0..b3 (si1 had block0
   hardcoded). Needed because sub-iter k's block bytes are chunk0 (32,40,48,56) etc, not (0,8,16,24). *)
let LEN_RECONCILE_GEN = prove
 (`!(m:byte) (b0:byte) (b1:byte) (b2:byte) (b3:byte).
     (!j. j < 8 ==> (bit j m <=>
        EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16] < 9))
     ==> LENGTH(ACC_IDX m) =
         LENGTH(REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3]:int32 list)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:byte`;
    `word(val(b0:byte) MOD 16):byte`; `word(val(b0:byte) DIV 16):byte`;
    `word(val(b1:byte) MOD 16):byte`; `word(val(b1:byte) DIV 16):byte`;
    `word(val(b2:byte) MOD 16):byte`; `word(val(b2:byte) DIV 16):byte`;
    `word(val(b3:byte) MOD 16):byte`; `word(val(b3:byte) DIV 16):byte`] ACC_LENGTH_EQ_FILTER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(fun (asl,gw) -> let n = rand(rator(lhand gw)) in
       MP_TAC(SPEC n (find (fun th -> is_forall(concl th) && can(find_term(fun u->match u with Const("EL",_)->true|_->false))(concl th)) (map snd asl)))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    W(fun (asl,gw) -> let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="val" && type_of(rand u)=`:byte` with _->false) gw in
       let bt = rand bt in
       MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN STRIP_TAC THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       REFL_TAC);
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LENGTH_FILTER_BYTE_NIBBLES_4_BYTES; LENGTH_REJ_SAMPLE_ETA4_BYTES]]);;

(* ACC1_IDENT_TAC: prove & ASSUME `LENGTH(REJ_SAMPLE(SUB_LIST(0,16i+4)))=acc1` (acc1 must be ABBREV'd
   as outlen0 + LENGTH(REJ_NIBBLES(SUB_LIST(16i,4))), outlen0 def + that ABBREV in asl). Re-run right
   before each fold (it gets consumed by the store-address restate). *)
let ACC1_IDENT_TAC : tactic =
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i`;`4`;`0`] SUB_LIST_SPLIT)] THEN
   REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_))->true|_->false)
       then ASSUME_TAC(REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA4_BYTES] th) else NO_TAC) THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA4",_),_))),Var("outlen0",_))->true|_->false)
       then REWRITE_TAC[th] else NO_TAC) THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),_),Var("acc1",_))->can(find_term(fun u->u=`outlen0:num`))(concl th)|_->false) then (MP_TAC th THEN ARITH_TAC) else NO_TAC); ALL_TAC];;
