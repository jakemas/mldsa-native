(* MID_EXIT_SUBITER2: sub-iter-2 mid-guard fires TAKEN -> pc+318 at pos 16i+8.
   Entry pc+56/pos=16i (q56-style), niblen(16i+4)<=248 (mg1 not taken), niblen(16i+8)>248
   (mg2 taken), 16(i+1)<=272. Reaches pc+318 with RCX=16i+8, RAX=niblen(16i+8),
   store=REJ_SAMPLE(0,16i+8).
   Composes: prefix-monotonicity prelude (niblen(16i)<=248) + PREFIX_TO_S21 + MG1_NT (mg1 not
   taken -> pc+167) + SI1_FOLD_V2 + purge leftover COND-RIP-s23 + SI2_BODY (gather/store/counter
   to s33) + SI2_MG2_TAKEN (mg2 taken -> pc+318) + ENSURES_FINAL + RAX/RCX/guard discharge.
   Load after: full CLEAN_BODY chain, .midexit_prefix (PREFIX_TO_S21_TAC), .mg1_nt (MG1_NT_TAC),
   .subiter_bridge_lemmas, .midexit_subiter1 (RCX4_COLLAPSE). VALIDATED interactively 2026-06-24. *)

(* SI2_BODY_TAC: SI2_INTEGRATED body (gather/store-fold/counter to s33) w/o the not-taken mg2 resolve. *)
let SI2_BODY_TAC : tactic =
  REABBREV_TAC `mask8b = read R8 s23` THEN
  ABBREV_TAC `acc1 = outlen0 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` THEN
  ACC1_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1`]) THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (24--24) THEN
  X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s25" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s24 = mask8b:int64`]) THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (26--26) THEN TAB2_TEQ_TAC THEN REABBREV_TAC `tab2 = read YMM6 s26` THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (27--27) THEN REABBREV_TAC `pshuf2 = read YMM6 s27` THEN
  PURGE_STALE_STATES_TAC ["s26"] THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (28--28) THEN REABBREV_TAC `sx2 = read YMM1 s28` THEN
  VAL_INT64_TAC `acc1:num` THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (29--29) THEN
  SUBGOAL_THEN `sx2:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf2:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx2def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx2:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx2def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_2 ASSUME_TAC THENL [MASKBIT_TGT_2_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_2 ASSUME_TAC THENL [PF_PROOF_2; ALL_TAC]) THEN
  ACC1_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg2 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c) asms in
    let mthm2 = find (fun th -> concl th = maskbit_tgt_2) asms in
    let pfth2 = find (fun th -> concl th = pf_target_2) asms in
    let sx2u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx2",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s29",_))),Var("sx2",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth2] (REWRITE_RULE[sx2u] storef0) in
    let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8b:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc1)):int64`; `s29:x86state`; g2; m; `LENGTH(ACC_IDX (word (val (mask8b:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g2; m; `word_subword (chunk0:int128) (32,8):byte`; `word_subword (chunk0:int128) (40,8):byte`; `word_subword (chunk0:int128) (48,8):byte`; `word_subword (chunk0:int128) (56,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm2 bg2)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (32,8):byte`;`word_subword (chunk0:int128) (40,8):byte`;`word_subword (chunk0:int128) (48,8):byte`;`word_subword (chunk0:int128) (56,8):byte`] LEN_RECONCILE_GEN) mthm2 in
    let lr = REWRITE_RULE[GSYM blk1_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk1_eq] rej_store in
    let acc1_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc1",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s29",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc1:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc1_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc1_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s29:x86state`;m;`SUB_LIST(16*i+4,4) (inlist:byte list)`;`SUB_LIST(0,16*i+4) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+4`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+4)+4 = 16*i+8`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (30--33);;

(* SI2_MG2_TAKEN_TAC: from s33, resolve mid-guard-2 TAKEN (niblen(16i+8)>248) -> RIP s35 = pc+318. *)
let SI2_MG2_TAKEN_TAC : tactic =
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
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] OUTLEN0_LE_256_FROM_SUBITER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block1len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc1:num` block1len in
    let bridge2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_) -> true | _ -> false) asl) in
    let lt32 = REWRITE_RULE[SYM bridge2] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32`) asl)) in
    let pop_len2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let gt248 = REWRITE_RULE[SYM bridge2] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len2 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (34--35) THEN
  SUBGOAL_THEN `read RIP s35 = word (pc + 318):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let pop_len2_old = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
      let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
      let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2_old) in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asl in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 318`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[pop_len2_typed] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;

let me2_pre = midexit1_pre;;
let me2_post =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 318) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+8) inlist):int32 list)) /\
       read RCX s = word(16*i+8) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+8) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+8) inlist))`;;

let midexit2_tm =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
  mk_imp(list_mk_conj([`LENGTH (inlist:byte list) = 272`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(res:int64),1024)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(table:int64),2048)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
    `16 * (i + 1) <= 272`;
    `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 248`;
    `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`]),
    list_mk_comb(`ensures x86`,[me2_pre; me2_post; midexit1_cframe])));;

let MID_EXIT_SUBITER2 = prove(midexit2_tm,
  PREFIX_TO_S21_TAC THEN
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
  MG1_NT_TAC THEN SI1_FOLD_V2 THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s23",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI2_BODY_TAC THEN
  SI2_MG2_TAKEN_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* discharge if-guard (taken), RAX collapse, RCX collapse *)
  W(fun (asl,w) ->
    let pop_len2 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2) in
    let rax_red0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    let bridge2 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_) -> true | _ -> false) asl in
    REWRITE_TAC[pop_len2_typed; snd rax_red0; snd bridge2]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  (* RCX collapse: double +4 nest *)
  MP_TAC(SPEC `16*i` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `16*i+4` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `16*i+4+4 = 16*i+8`] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  AP_TERM_TAC THEN ARITH_TAC);;

Printf.printf "MID_EXIT_SUBITER2 proved, hyps=%d\n" (List.length(hyp MID_EXIT_SUBITER2));;
