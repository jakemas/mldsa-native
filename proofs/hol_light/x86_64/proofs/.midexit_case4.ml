(* MID_EXIT_CASE4: all 4 sub-iters of the i=N-1-style block run clean (niblen(16i+4),16i+8,16i+12
   <=248), then at the loop back-edge pc+56/pos16(i+1) the head-guard1 (cmp eax,248) fires TAKEN
   since niblen(16(i+1))>248 -> pc+318 at pos16(i+1).
   Entry pc+56/pos=16i; hyps niblen(16i+12)<=248 (=> niblen(16i+4),16i+8 <=248 by mono),
   niblen(16(i+1))>248, 16(i+1)<=272. Reaches pc+318 with RCX=16(i+1), RAX=niblen(16(i+1)),
   store=REJ_SAMPLE(0,16(i+1)).
   Composes: PREFIX_TO_S21 + MG1_NT + SI1_FOLD + purge + SI2_BODY + MG2_NT + purge + SI3_BODY3
   + MG3_NT + purge + SI4_BODY4 (back-edge s57) + RAX-fold + head-guard1 eax-TAKEN (s58-59) +
   ENSURES_FINAL + RCX/store discharge. Load after .mg1_nt/.mg2_nt/.mg3_nt/.midexit_subiter2(SI2_BODY)
   /.midexit_subiter3(SI3_BODY3)/.si4_body4/.midexit_subiter1(RCX4_COLLAPSE). VALIDATED 2026-06-24. *)

let me4_post =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 318) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list)) /\
       read RCX s = word(16*(i+1)) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist))`;;

let midexit4_tm =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
  mk_imp(list_mk_conj([`LENGTH (inlist:byte list) = 272`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(res:int64),1024)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(table:int64),2048)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
    `16 * (i + 1) <= 272`;
    `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) <= 248`;
    `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`]),
    list_mk_comb(`ensures x86`,[midexit1_pre; me4_post; midexit1_cframe])));;

let MID_EXIT_CASE4 = prove(midexit4_tm,
  PREFIX_TO_S21_TAC THEN
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
  MG1_NT_TAC THEN SI1_FOLD_V2 THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s23",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI2_BODY_TAC THEN MG2_NT_TAC THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s35",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI3_BODY3_TAC THEN MG3_NT_TAC THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s47",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI4_BODY4_TAC THEN
  (* niblen(16(i+1))<=256 *)
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) <= 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+12`] OUTLEN0_LE_256_FROM_SUBITER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc3",_))->true|_->false) then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+12)+4 = 16*(i+1)`; ARITH_RULE `16*i+16=16*(i+1)`]; ALL_TAC] THEN
  (* bridge4 *)
  SUBGOAL_THEN `acc3 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+12,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+12`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+12)+4 = 16*(i+1)`; ARITH_RULE `16*i+16 = 16*(i+1)`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* pop_len4 + rax_red0 *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let m8d_val = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8d:int64` && can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))(concl th) | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt4 = REWRITE_RULE[m8d_val] (REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE3))) in
    let lanesum = rand(concl popcnt4) in
    let mb4 = find_a (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`24` | _ -> false))c) in
    let mb4_tm = concl mb4 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in
    let block3 = `[word_subword (chunk0:int128) (96,8); word_subword chunk0 (104,8); word_subword chunk0 (112,8); word_subword chunk0 (120,8)]:byte list` in
    let block3len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block3)) in
    let bsum4_raw = prove(mk_imp(mb4_tm, mk_eq(lanesum, block3len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len4 = REWRITE_RULE[GSYM blk3_eq] (TRANS popcnt4 (MP bsum4_raw mb4)) in
    let bridge4 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_)))->true|_->false) in
    let le256 = find_a (fun th -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) <= 256`) in
    let lt32 = REWRITE_RULE[SYM bridge4] (MATCH_MP (ARITH_RULE `a<=256 ==> a < 2 EXP 32`) le256) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    ASSUME_TAC pop_len4 THEN ASSUME_TAC rax_red0) THEN
  (* fold RAX s57 -> word(niblen(16(i+1))) *)
  W(fun (asl,w) ->
    let pl4 = find (fun (_,th) -> match concl th with Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> can(find_term(fun u->u=`mask8d:int64`))(concl th) | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> can(find_term(fun u->u=`acc3:num`))(concl th) | _ -> false) asl in
    let bridge4 = find (fun (_,th) -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_)))->true|_->false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl4]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd bridge4])) THEN
  (* head-guard1 eax TAKEN -> pc+318 *)
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let gt248 = find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`) asl in
    let lt32 = find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) < 2 EXP 32`) asl in
    let ja_taken = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`; `248`] JA_TAKEN_GT) (CONJ (snd gt248) (snd lt32)) in
    ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (58--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `16*(i+1) = 16*i+16`] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(16 * i + 4) MOD 2 EXP 32 = 16 * i + 4 /\ (16 * i + 4) MOD 2 EXP 64 = 16 * i + 4 /\
                  (16 * i + 8) MOD 2 EXP 32 = 16 * i + 8 /\ (16 * i + 8) MOD 2 EXP 64 = 16 * i + 8 /\
                  (16 * i + 12) MOD 2 EXP 32 = 16 * i + 12 /\ (16 * i + 12) MOD 2 EXP 64 = 16 * i + 12 /\
                  (16 * i + 16) MOD 2 EXP 32 = 16 * i + 16 /\ (16 * i + 16) MOD 2 EXP 64 = 16 * i + 16`
       STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD] THEN
    SUBGOAL_THEN `(16 * i) MOD 2 EXP 64 = 16 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`; ARITH_RULE `(16*i+8)+4 = 16*i+12`;
                ARITH_RULE `(16*i+12)+4 = 16*i+16`; ARITH_RULE `16*i+4+4 = 16*i+8`; ARITH_RULE `16*i+8+4 = 16*i+12`;
                ARITH_RULE `16*i+12+4 = 16*i+16`]));
    ASM_REWRITE_TAC[]]);;

Printf.printf "MID_EXIT_CASE4 proved, hyps=%d\n" (List.length(hyp MID_EXIT_CASE4));;
