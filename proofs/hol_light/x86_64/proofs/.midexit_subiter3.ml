(* MID_EXIT_SUBITER3: sub-iter-3 mid-guard fires TAKEN -> pc+318 at pos 16i+12.
   Entry pc+56/pos=16i, niblen(16i+8)<=248 (mg1,mg2 not taken), niblen(16i+12)>248 (mg3 taken),
   16(i+1)<=272. Reaches pc+318 with RCX=16i+12, RAX=niblen(16i+12), store=REJ_SAMPLE(0,16i+12).
   Load after: full CLEAN_BODY chain, .midexit_prefix, .mg1_nt, .mg2_nt, .midexit_subiter2 (SI2_BODY_TAC),
   .midexit_subiter1 (RCX4_COLLAPSE), .subiter_bridge_lemmas, .si3_full/.si3_integrated/.si3_fold_pieces
   (SI3_TAIL uses ACC2_IDENT_TAC, TAB3_TEQ_TAC, MASKBIT_TGT_3_TAC, PF_PROOF_3, etc.).
   VALIDATED interactively 2026-06-24. *)

let SI3_BODY3_TAC : tactic =
  ABBREV_TAC `acc2 = acc1 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (16*i+4,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8c = read R8 s35` THEN
  SUBGOAL_THEN `acc2 <= 248` ASSUME_TAC THENL
   [(* after ABBREV acc2, the bridge2 (acc1+niblen(16i+4,4)=niblen_sample(16i+8)) folds to
       (acc2 = niblen_sample(16i+8)); SUBST it then ACCEPT niblen(16i+8)<=248. *)
    FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Var("acc2",_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_)))->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (* case-4: niblen(16i+8)<=248 from niblen(16i+12)<=248 by monotonicity *)
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA4_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  VAL_INT64_TAC `acc2:num` THEN
  ACC2_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2`]) THEN
  X86_VSTEPS_TAC EXEC (36--36) THEN
  X86_VERBOSE_STEP_TAC EXEC "s37" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s36 = mask8c:int64`]) THEN
  X86_VSTEPS_TAC EXEC (38--38) THEN TAB3_TEQ_TAC THEN REABBREV_TAC `tab3 = read YMM6 s38` THEN
  X86_VSTEPS_TAC EXEC (39--39) THEN REABBREV_TAC `pshuf3 = read YMM6 s39` THEN
  PURGE_STALE_STATES_TAC ["s38"] THEN
  X86_VSTEPS_TAC EXEC (40--40) THEN REABBREV_TAC `sx3 = read YMM1 s40` THEN
  VAL_INT64_TAC `acc2:num` THEN
  X86_STEPS_TAC EXEC (41--41) THEN
  SUBGOAL_THEN `sx3:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf3:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx3def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx3:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx3def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_3 ASSUME_TAC THENL [MASKBIT_TGT_3_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_3 ASSUME_TAC THENL [PF_PROOF_3; ALL_TAC]) THEN
  ACC2_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg3 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        not(can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm3 = find (fun th -> concl th = maskbit_tgt_3) asms in
    let pfth3 = find (fun th -> concl th = pf_target_3) asms in
    let sx3u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx3",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s41",_))),Var("sx3",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth3] (REWRITE_RULE[sx3u] storef0) in
    let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
    let m = `word (val (mask8c:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc2)):int64`; `s41:x86state`; g3; m; `LENGTH(ACC_IDX (word (val (mask8c:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g3; m; `word_subword (chunk0:int128) (64,8):byte`; `word_subword (chunk0:int128) (72,8):byte`; `word_subword (chunk0:int128) (80,8):byte`; `word_subword (chunk0:int128) (88,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm3 bg3)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (64,8):byte`;`word_subword (chunk0:int128) (72,8):byte`;`word_subword (chunk0:int128) (80,8):byte`;`word_subword (chunk0:int128) (88,8):byte`] LEN_RECONCILE_GEN) mthm3 in
    let lr = REWRITE_RULE[GSYM blk2_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk2_eq] rej_store in
    let acc2_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc2",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s41",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc2:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc2_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc2_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s41:x86state`;m;`SUB_LIST(16*i+8,4) (inlist:byte list)`;`SUB_LIST(0,16*i+8) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+8`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+8)+4 = 16*i+12`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC EXEC (42--45) THEN
  ALL_TAC;;

(* SI3_MG3_TAKEN_TAC: from s45, resolve mid-guard-3 TAKEN (niblen(16i+12)>248) -> RIP s47=pc+318. *)
let SI3_MG3_TAKEN_TAC : tactic =
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
    let gt248 = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (46--47) THEN
  SUBGOAL_THEN `read RIP s47 = word (pc + 318):int64` ASSUME_TAC THENL
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
      let ja = find_a (fun th -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 318`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;

let me3_post =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 318) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+12) inlist):int32 list)) /\
       read RCX s = word(16*i+12) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+12) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+12) inlist))`;;

let midexit3_tm =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
  mk_imp(list_mk_conj([`LENGTH (inlist:byte list) = 272`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(res:int64),1024)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(table:int64),2048)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
    `16 * (i + 1) <= 272`;
    `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) <= 248`;
    `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`]),
    list_mk_comb(`ensures x86`,[midexit1_pre; me3_post; midexit1_cframe])));;

let MID_EXIT_SUBITER3 = prove(midexit3_tm,
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
  SI3_BODY3_TAC THEN SI3_MG3_TAKEN_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* discharge: RAX (block2 4-list -> SUB_LIST + pop_len3 + rax_red0 + bridge3), guard (JA_TAKEN_GT), RCX *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let pop_len3 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) in
    let rax_red0 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
    let bridge3 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> can(find_term(fun u->match u with Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))->true|_->false))(concl th) | _ -> false) in
    REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[pop_len3] THEN REWRITE_TAC[rax_red0; bridge3]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  SUBGOAL_THEN `(16 * i + 4) MOD 2 EXP 32 = 16 * i + 4 /\ (16 * i + 4) MOD 2 EXP 64 = 16 * i + 4 /\
                (16 * i + 8) MOD 2 EXP 32 = 16 * i + 8 /\ (16 * i + 8) MOD 2 EXP 64 = 16 * i + 8 /\
                (16 * i + 12) MOD 2 EXP 32 = 16 * i + 12 /\ (16 * i + 12) MOD 2 EXP 64 = 16 * i + 12`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD] THEN
  SUBGOAL_THEN `(16 * i) MOD 2 EXP 64 = 16 * i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  ASM_REWRITE_TAC[ARITH_RULE `16*i+4+4 = 16*i+8`; ARITH_RULE `16*i+8+4 = 16*i+12`] THEN
  REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(16*i+8)+4 = 16*i+12`]);;

Printf.printf "MID_EXIT_SUBITER3 proved, hyps=%d\n" (List.length(hyp MID_EXIT_SUBITER3));;
