(* Sub-iter 3: from RIP=pc+215 (after SI2_RESOLVE) to RIP=pc+268 (mid-guard 3 fall-through).
   Mask = mask8c (R8 ushr16, byte 2 -> lanes 16-23, block2 = SUB_LIST(16i+8,4)). Uses PREFIX4's
   lanes-16..23 maskbit + POPCNT_BYTE2. Requires SI2 chain already applied (RIP=pc+215, RAX still
   the unfolded sub-iter-2 popcount nest). *)

(* SI3_PRE: fold RAX s35 -> word acc2, abbrev acc2, reabbrev mask8c, establish acc2<=248. *)
let SI3_PRE : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let pop_len2_old = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asms in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) pop_len2_old in
    let rax_red0 = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asms in
    RULE_ASSUM_TAC(REWRITE_RULE[pop_len2_typed]) THEN RULE_ASSUM_TAC(REWRITE_RULE[rax_red0])) THEN
  ABBREV_TAC `acc2 = acc1 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (16*i+4,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8c = read R8 s35` THEN
  (* bound acc2 + niblen(16i+8,4) <= 248, then acc2 <= 248 *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 272`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=272 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd3 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_3) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let bnd3a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd3 in
    let bnd3b = REWRITE_RULE[acc1_def] bnd3a in
    let bnd3c = REWRITE_RULE[acc2_def] (REWRITE_RULE[ADD_ASSOC] bnd3b) in
    ASSUME_TAC bnd3c THEN
    ASSUME_TAC (MATCH_MP (ARITH_RULE `acc2 + x <= 248 ==> acc2 <= 248`) bnd3c)) THEN
  VAL_INT64_TAC `acc2:num`;;

(* SI3_GATHER: vextracti128 hi (s36), movzbl capture (s37), gather, store-safe, counter -> RIP pc+261. *)
let SI3_GATHER : tactic =
  X86_VSTEPS_TAC EXEC (36--36) THEN
  X86_VERBOSE_STEP_TAC EXEC "s37" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s36 = mask8c:int64`]) THEN
  X86_VSTEPS_TAC EXEC (38--38) THEN REABBREV_TAC `tab3 = read YMM6 s38` THEN
  X86_VSTEPS_TAC EXEC (39--39) THEN REABBREV_TAC `pshuf3 = read YMM6 s39` THEN
  PURGE_STALE_STATES_TAC ["s38"] THEN
  X86_VSTEPS_TAC EXEC (40--40) THEN REABBREV_TAC `sx3 = read YMM1 s40` THEN
  X86_STEPS_TAC EXEC (41--45);;

(* SI3_MG: forward facts pop_len3/bnd3c'/rax_red0_3/ja3 for mid-guard 3. *)
let SI3_MG : tactic =
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
    let blk2_eq = el 2 (CONJUNCTS bb) in   (* SUB_LIST(16*i+8,4) = [chunk0 64,72,80,88] *)
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
    let bnd3c = find_a (fun th -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> true | _ -> false) in
    let block2len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+8,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd3c in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `acc2:num` block2len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd3c (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja);;

(* SI3_RESOLVE: step cmp/ja (s46-47), typed-popcount branch resolution -> RIP s47 = pc+268. *)
let SI3_RESOLVE : tactic =
  X86_STEPS_TAC EXEC (46--47) THEN
  SUBGOAL_THEN `read RIP s47 = word (pc + 268):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      (* The counter step already folded popcnt->LENGTH(REJ_NIBBLES[explicit block2]) into the COND.
         Convert that explicit block2 to SUB_LIST(16i+8,4) form via GSYM blk2_eq so rax_red0/ja match. *)
      let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
      let blk16 = find_a (fun th -> is_eq(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
      let blk2_eq = el 2 (CONJUNCTS bb) in
      let rax_red0 = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) asms in
      let ja = find (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) asms in
      let ifrip = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s47",_))),r) ->
           (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false) | _ -> false) asms in
      MP_TAC ifrip THEN REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;
