(* Sub-iter-2 table-load bridge: R_EQ_B/RLT_B (mask8b zx-collapse + bound) + TAB2_TEQ_TAC.
   At s26 (after the vmovq table load), read YMM6 s26 = word_zx(word_zx(read(bytes64(table+8*r)) s25))
   with r = val(word_zx(word_zx(word(val mask8b MOD 256)))). Same shape as si1's tab1 but mask8b/s25/s26.
   After REABBREV tab2, gives teq2: word_zx(word_zx(word(nwl(TABLE_ENTRY(word(val mask8b MOD 256)))))) = tab2. *)
let R_EQ_B = prove(`val (word_zx (word_zx (word (val (mask8b:int64) MOD 256):byte):int32):int64):num = val (mask8b:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;
let RLT_B = prove(`val (mask8b:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;
let TAB2_TEQ_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let tblinv = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s25",_))),_) ->
         can(find_term(fun u->u=`mldsa_rej_uniform_table:byte list`)) (concl th) | _ -> false) asms in
    let tvr = MP (ISPECL[`table:int64`;`val (mask8b:int64) MOD 256`;`s25:x86state`] TABLE_VMOVQ_READ) (CONJ tblinv RLT_B) in
    let ymm6 = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("YMM6",_)),Var("s26",_))),_)->true|_->false) asms in
    let ymm6' = REWRITE_RULE[R_EQ_B; tvr] ymm6 in
    ASSUME_TAC ymm6');;
