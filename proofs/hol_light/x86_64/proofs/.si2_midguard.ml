let SI2_MG_TAC : tactic =
W(fun (asl,w) ->
  let asms = map snd asl in
  let find_a p = find p asms in
  let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
  let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
  let popcnt2 = REWRITE_RULE[m8b_def]
     (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE1)) in
  let lanesum8 = rand(concl popcnt2) in
  let mb2 = find_a (fun th -> let c=concl th in is_forall c &&
     can(find_term(fun u->u=`f1bnd:int256`))c &&
     can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),_) -> true | _ -> false))c) in
  let mb2_tm = concl mb2 in
  let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
  let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
  let blk16 = find_a (fun th -> is_eq(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
          length(dest_list(rand(concl th)))=16 with _->false)) in
  let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
              (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le))
                    blk16) in
  let blk1_eq = el 1 (CONJUNCTS bb) in
  let block1 = `[word_subword (chunk0:int128) (32,8); word_subword chunk0 (40,8);
                 word_subword chunk0 (48,8); word_subword chunk0 (56,8)]:byte list` in
  let block1len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block1)) in
  let bsum2_raw = prove(mk_imp(mb2_tm, mk_eq(lanesum8, block1len_x)),
    DISCH_THEN(fun mbthm ->
      let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
        CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
          (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
      REWRITE_TAC mbs) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
    REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
    SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
  (* fold explicit block1 -> SUB_LIST(16i+4,4) via blk1_eq (GSYM) *)
  let pop_len2 = REWRITE_RULE[GSYM blk1_eq] (TRANS popcnt2 (MP bsum2_raw mb2)) in
  (* bound: outlen0 + niblen(block0) + block1len <= 248 *)
  let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 256`) in
  let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
  let a1 = MP (MP (ARITH_RULE `16*(i+1)<=256 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
  let bnd2 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_2) (CONJ a1 nibbnd) in
  (* acc1 = outlen0 + niblen(block0); outlen0 = LENGTH(REJ_SAMPLE...(SUB_LIST(0,16i))). Rewrite bnd2's
     first two terms into acc1. *)
  let outlen0_def = find_a (fun th -> match concl th with
     Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
  let acc1_def = find_a (fun th -> match concl th with
     Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),_),_)),Var("acc1",_)) -> true | _ -> false) in
  (* bnd2 : LENGTH(REJ_SAMPLE(SUB_LIST(0,16i))) + niblen(SUB_LIST(16i,4)) + block1len <= 248
     rewrite LENGTH(REJ_SAMPLE...) -> outlen0, then (outlen0 + niblen(...)) -> acc1. *)
  let bnd2a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd2 in
  let bnd2c = REWRITE_RULE[acc1_def] bnd2a in
  (* bnd2c : acc1 + block1len <= 248 *)
  let block1len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
  let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd2c in
  let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
  let ja = MP (ISPECL[mk_binop `(+):num->num->num` `acc1:num` block1len; `248`] JA_NOT_TAKEN_LE)
              (CONJ bnd2c (ARITH_RULE `248 < 2 EXP 32`)) in
  (let oc=open_out "/tmp/si2_facts.txt" in
   output_string oc ("pop_len2: "^string_of_term(concl pop_len2)^"\n\nbnd2c: "^string_of_term(concl bnd2c)^
     "\n\nrax_red0: "^string_of_term(concl rax_red0)^"\n\nja: "^string_of_term(concl ja)); close_out oc);
  ASSUME_TAC pop_len2 THEN ASSUME_TAC bnd2c THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja);;
