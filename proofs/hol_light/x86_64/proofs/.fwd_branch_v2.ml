  (* === REORDERED branch resolution (NO RULE_ASSUM over s21 state) === *)
  W(fun (asl,w) ->
    (* 1. popeq: word_popcount(word_zx^3(word(val mask8 MOD 256))) = bitsum8(low8 of f1bnd) *)
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s21",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    (* 2. bitsum8 = LENGTH(REJ_NIBBLES block0) via maskbit forall + block byte facts *)
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c) asl) in
    let mb_tm = concl maskbit in
    let mb_assumed = ASSUME mb_tm in
    let mbits = map (fun k -> let th=SPEC(mk_small_numeral k) mb_assumed in
         CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    (* combined: word_popcount(...) = LENGTH(REJ_NIBBLES block0) *)
    let pop_len = TRANS popeq bsum in
    (* 3. bound: outlen0 + LENGTH(REJ_NIBBLES block0) <= 248 *)
    let leninl = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asl in
    let i116 = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asl in
    let nible = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA4",_),_))),_) -> true | _ -> false) asl in
    let len_eq = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asl in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=256 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`)
                    (snd i116)) (snd leninl) in
    let bnd0 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_1) (CONJ a1 (snd nible)) in
    let bnd = REWRITE_RULE[snd len_eq] bnd0 in  (* outlen0 + LENGTH(REJ_NIBBLES block0) <= 248 *)
    (* 4. RAX collapse: word_zx(word_add(word_zx(word outlen0))(word_zx(word_zx(word popcount)))) = word(outlen0+block0len) *)
    let block0len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in  (* word_zx(...word outlen0...word block0len...) = word(outlen0+block0len) *)
    (* but RAX has popcount, not block0len; rewrite popcount->block0len first via pop_len *)
    let rax_red = REWRITE_RULE[pop_len] (GSYM(REWRITE_RULE[GSYM pop_len] (SYM rax_red0))) in
    (* JA_NOT_TAKEN: outlen0+block0len <= 248 *)
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `outlen0:num` block0len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    (let oc=open_out "/tmp/reorder_facts.txt" in
     output_string oc ("pop_len: "^string_of_term(concl pop_len)^"\n\nrax_red0: "^string_of_term(concl rax_red0)^
       "\n\nja: "^string_of_term(concl ja)^"\n\nbnd: "^string_of_term(concl bnd)^"\n"); close_out oc);
    (* stash these as assumptions for the step *)
    ASSUME_TAC pop_len THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (22--23) THEN
  (* resolve the ja branch: RIP s23 = pc+163 (fall through to sub-iter 2) *)
  SUBGOAL_THEN `read RIP s23 = word (pc + 163):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th)) asl in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 163`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* fold RAX read clean using the assumed pop_len + rax_red0 (now in asl) *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr])) THEN
