(* SI3_INTEGRATED_MS: full sub-iter-3 (gather + store-fold + counter + mid-guard), cheat-free.
   From s35 (RIP=pc+215, running store SUB_LIST(0,16i+8)) to s47 (RIP=pc+268), store folded to
   SUB_LIST(0,16i+12). Deps: .si3_full (SI3_PRE/GATHER/MG/RESOLVE), .si3_fold_pieces, .si2_fold_complete
   (LEN_RECONCILE_GEN), .pf_target_proof. g3 = hi 128 lane (no shift) so gthm=bg3 directly. *)
let SI3_INTEGRATED_MS : tactic =
  SI3_PRE THEN              (* abbrev acc2, reabbrev mask8c, bounds; RAX folded to word acc2 *)
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
  X86_STEPS_KEEPEV_TAC EXEC (41--41) THEN
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
  X86_STEPS_KEEPEV_TAC EXEC (42--45) THEN
  SI3_MG THEN SI3_RESOLVE_MS;;
