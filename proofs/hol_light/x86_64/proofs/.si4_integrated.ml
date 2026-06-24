(* SI4_INTEGRATED: full sub-iter-4 (gather + store-fold + counter + jmp), cheat-free.
   From s47 (RIP=pc+272, running store SUB_LIST(0,16i+12)) to s57 (RIP=pc+56, back-edge),
   store folded to SUB_LIST(0,16i+16). NO mid-guard. g4 = hi 128 lane >>64. Deps: .si4_full
   (SI4_PRE/GATHER), .si4_fold_pieces, .si2_fold_complete (LEN_RECONCILE_GEN), .pf_target_proof. *)
let SI4_INTEGRATED : tactic =
  SI4_PRE THEN
  ACC3_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3`]) THEN
  X86_VSTEPS_TAC EXEC (48--48) THEN
  X86_VERBOSE_STEP_TAC EXEC "s49" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s48 = mask8d:int64`]) THEN
  X86_VSTEPS_TAC EXEC (50--50) THEN TAB4_TEQ_TAC THEN REABBREV_TAC `tab4 = read YMM6 s50` THEN
  X86_VSTEPS_TAC EXEC (51--51) THEN REABBREV_TAC `pshuf4 = read YMM6 s51` THEN
  PURGE_STALE_STATES_TAC ["s50"] THEN
  X86_VSTEPS_TAC EXEC (52--52) THEN REABBREV_TAC `sx4 = read YMM1 s52` THEN
  VAL_INT64_TAC `acc3:num` THEN
  X86_STEPS_TAC EXEC (53--53) THEN
  SUBGOAL_THEN `sx4:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf4:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx4def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx4:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx4def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_4 ASSUME_TAC THENL [MASKBIT_TGT_4_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_4 ASSUME_TAC THENL [PF_PROOF_4; ALL_TAC]) THEN
  ACC3_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg4 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm4 = find (fun th -> concl th = maskbit_tgt_4) asms in
    let pfth4 = find (fun th -> concl th = pf_target_4) asms in
    let sx4u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx4",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s53",_))),Var("sx4",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth4] (REWRITE_RULE[sx4u] storef0) in
    let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8d:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc3)):int64`; `s53:x86state`; g4; m; `LENGTH(ACC_IDX (word (val (mask8d:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g4; m; `word_subword (chunk0:int128) (96,8):byte`; `word_subword (chunk0:int128) (104,8):byte`; `word_subword (chunk0:int128) (112,8):byte`; `word_subword (chunk0:int128) (120,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm4 bg4)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (96,8):byte`;`word_subword (chunk0:int128) (104,8):byte`;`word_subword (chunk0:int128) (112,8):byte`;`word_subword (chunk0:int128) (120,8):byte`] LEN_RECONCILE_GEN) mthm4 in
    let lr = REWRITE_RULE[GSYM blk3_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk3_eq] rej_store in
    let acc3_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc3",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s53",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc3:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc3_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc3_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s53:x86state`;m;`SUB_LIST(16*i+12,4) (inlist:byte list)`;`SUB_LIST(0,16*i+12) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+12`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+12)+4 = 16*i+16`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC EXEC (54--57);;
