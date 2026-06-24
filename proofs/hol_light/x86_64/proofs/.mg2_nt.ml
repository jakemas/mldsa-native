(* MG2_NT_TAC: from s33, resolve mid-guard-2 NOT-taken (niblen(16i+8)<=248 direct) -> RIP s35=pc+219.
   = SI2_MG2_TAKEN's pop_len2/bridge2 build but JA_NOT_TAKEN_LE + RIP pc+219, ending with RAX-fold
   so the SI3 store memsafe at s41 discharges. *)
let MG2_NT_TAC : tactic =
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
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
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
    let pop_len2 = REWRITE_RULE[GSYM blk1_eq] (TRANS popcnt2 (MP bsum2_raw mb2)) in
    ASSUME_TAC pop_len2) THEN
  (* bridge2: acc1 + niblen(SUB(16i+4,4)) = niblen_sample(16i+8) = (acc2 conceptually) *)
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* bnd: acc1 + block1len <= 248 (= niblen(16i+8)<=248 direct hyp) *)
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list) <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (* case-4: niblen(16i+8)<=248 follows from niblen(16i+12)<=248 by monotonicity *)
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA4_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block1len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc1:num` block1len in
    let bnd = snd(find (fun (_,th) -> concl th = mk_binop `(<=):num->num->bool` sum `248`) asl) in
    let pop_len2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL [sum; `248`] JA_NOT_TAKEN_LE) (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len2 THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (34--35) THEN
  SUBGOAL_THEN `read RIP s35 = word (pc + 219):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let pop_len2_old = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
      let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
      let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2_old) in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asl in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 219`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[pop_len2_typed] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* RAX-fold so SI3 store memsafe discharges *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pl_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pl) in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[pl_typed]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]));;
