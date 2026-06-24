(* MG3_NT_TAC: from s45, mid-guard-3 NOT-taken from direct niblen(16i+12)<=248 -> RIP s47=pc+272,
   with RAX-fold so the SI4 store memsafe at s53 discharges. Clone of SI3_MG3_TAKEN w/ JA_NOT_TAKEN_LE. *)
let MG3_NT_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt3 = REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE2)) in
    let lanesum = rand(concl popcnt3) in
    let mb3 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`16` | _ -> false))c) in
    let mb3_tm = concl mb3 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let block2 = `[word_subword (chunk0:int128) (64,8); word_subword chunk0 (72,8);
                   word_subword chunk0 (80,8); word_subword chunk0 (88,8)]:byte list` in
    let block2len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block2)) in
    let bsum3_raw = prove(mk_imp(mb3_tm, mk_eq(lanesum, block2len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len3 = REWRITE_RULE[GSYM blk2_eq] (TRANS popcnt3 (MP bsum3_raw mb3)) in
    ASSUME_TAC pop_len3) THEN
  (* bridge3: acc2 + niblen(SUB(16i+8,4)) = niblen_sample(16i+12) *)
  SUBGOAL_THEN `acc2 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+8,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] OUTLEN0_LE_256_FROM_SUBITER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block2len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+8,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc2:num` block2len in
    let bridge3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> true | _ -> false) asl) in
    let lt32 = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32`) asl)) in
    let pop_len3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let bnd = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) <= 248`) asl)) in
    let ja = MP (ISPECL [sum; `248`] JA_NOT_TAKEN_LE) (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (46--47) THEN
  SUBGOAL_THEN `read RIP s47 = word (pc + 272):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
      let blk16 = find_a (fun th -> is_eq(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
      let blk2_eq = el 2 (CONJUNCTS bb) in
      let rax_red0 = find_a (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
      let ja = find_a (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 272`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* RAX-fold so SI4 store memsafe discharges *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]));;
