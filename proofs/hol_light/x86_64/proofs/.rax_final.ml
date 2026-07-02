(* Discharge the RAX final-state subgoal (goal 0):
   word_zx(word_add(word_zx(word acc3))(word_zx(word_zx(word(word_popcount(mask8d-arg)))))) =
     word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16(i+1))))). *)
let RAX_FINAL_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let m8d_val = find_a (fun th -> match concl th with
        Comb(Comb(Const("=",_),_),r) -> r = `mask8d:int64` &&
          can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))(concl th) | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    (* popcnt4: fold SUM->mask8b->mask8c (forward), then mask8c-ushr-form -> mask8d via m8d_val *)
    let popcnt4 = REWRITE_RULE[m8d_val] (REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE3))) in
    let lanesum = rand(concl popcnt4) in
    (* lanes-24..31 maskbit *)
    let mb4 = find_a (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`24` | _ -> false))c) in
    let mb4_tm = concl mb4 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in   (* SUB_LIST(16*i+12,4) = [chunk0 96,104,112,120] *)
    let block3 = `[word_subword (chunk0:int128) (96,8); word_subword chunk0 (104,8);
                   word_subword chunk0 (112,8); word_subword chunk0 (120,8)]:byte list` in
    let block3len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block3)) in
    let bsum4_raw = prove(mk_imp(mb4_tm, mk_eq(lanesum, block3len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len4 = REWRITE_RULE[GSYM blk3_eq] (TRANS popcnt4 (MP bsum4_raw mb4)) in
    (* bound acc3 + block3len < 2^32 *)
    let bnd4d = find_a (fun th -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),_) -> true | _ -> false) in
    let block3len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+12,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd4d in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    (* rewrite goal: popcnt -> block3len, then rax_red0 -> word(acc3+block3len) *)
    REWRITE_TAC[pop_len4] THEN REWRITE_TAC[rax_red0]) THEN
  (* now goal: word(acc3 + block3len) = word(LENGTH(REJ_SAMPLE(SUB_LIST(0,16(i+1))))) *)
  AP_TERM_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let acc3_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_)) -> true | _ -> false) in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let af = MP (ISPECL [`inlist:byte list`; `i:num`] ACC_FULL_LEN)
                (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) in
    REWRITE_TAC[SYM acc3_def; SYM acc2_def; SYM acc1_def] THEN
    REWRITE_TAC[SYM outlen0_def] THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    MP_TAC af THEN ARITH_TAC);;
