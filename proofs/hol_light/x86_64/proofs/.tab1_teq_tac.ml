(* Table-load bridge: derive teq `tab1 = word_zx(word_zx(word(nwl(TABLE_ENTRY(word(val mask8 MOD 256))))))`
   at s14 from the raw vmovq read, via TABLE_VMOVQ_READ + R_EQ (zx-collapse) + RLT (r<256). This is
   the genuine table-correspondence the old fold cheated. After REABBREV tab1, ASSUMEd fact's lhand
   read YMM6 s14 -> tab1, giving the teq the pf_target proof needs. *)
let R_EQ = prove(`val (word_zx (word_zx (word (val (mask8:int64) MOD 256):byte):int32):int64):num = val (mask8:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;
let RLT = prove(`val (mask8:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;
let TAB1_TEQ_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let tblinv = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s13",_))),_) ->
         can(find_term(fun u->u=`mldsa_rej_uniform_table:byte list`)) (concl th) | _ -> false) asms in
    let tvr = MP (ISPECL[`table:int64`;`val (mask8:int64) MOD 256`;`s13:x86state`] TABLE_VMOVQ_READ) (CONJ tblinv RLT) in
    let ymm6 = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("YMM6",_)),Var("s14",_))),_)->true|_->false) asms in
    let ymm6' = REWRITE_RULE[R_EQ; tvr] ymm6 in
    ASSUME_TAC ymm6');;
