(* SI2_INTEGRATED_MS: complete sub-iter-2 = gather + store-fold + counter + mid-guard, cheat-free.
   From post-SI1 s23 (RIP=pc+163, si1 clean store for SUB_LIST(0,16i+4) present), reaches s35 RIP=pc+215
   with the running clean store folded to SUB_LIST(0,16i+8). Composes SI2_GATHER_TO_STORE +
   ACC1_IDENT/restate + the si2 fold W + SI2_MG_TAC + SI2_RESOLVE.
   Load deps: .pf_target_proof, .maskbit_tgt_2_tac, .tab2_teq_tac, .si2_fold_pieces, .si2_fold_complete, .si2_full.
   NB the si1 store must FIRST be restated to bytes(res,4*acc1) (via ACC1_IDENT) BEFORE the gather, so it
   carries past the s29 vpmovdqu. *)
let si2mk f m = (fun g -> (let oc=open_out f in output_string oc m; close_out oc); ALL_TAC g);;
let SI2_INTEGRATED_MS : tactic =
  si2mk "/tmp/si2_0.txt" "SI2 entered" THEN
  REABBREV_TAC `mask8b = read R8 s23` THEN
  ABBREV_TAC `acc1 = outlen0 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` THEN
  ACC1_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1`]) THEN
  si2mk "/tmp/si2_acc1.txt" "acc1 done" THEN
  X86_VSTEPS_TAC EXEC (24--24) THEN
  si2mk "/tmp/si2_v24.txt" "vstep24 done" THEN
  X86_VERBOSE_STEP_TAC EXEC "s25" THEN
  si2mk "/tmp/si2_s25.txt" "s25 step done (pre movzbl-capture)" THEN
  MOVZBL_R10_CAPTURE_MS_TAC THEN
  si2mk "/tmp/si2_movzbl.txt" "movzbl s25 done" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s24 = mask8b:int64`]) THEN
  X86_VSTEPS_TAC EXEC (26--26) THEN TAB2_TEQ_TAC THEN REABBREV_TAC `tab2 = read YMM6 s26` THEN
  X86_VSTEPS_TAC EXEC (27--27) THEN REABBREV_TAC `pshuf2 = read YMM6 s27` THEN
  PURGE_STALE_STATES_TAC ["s26"] THEN
  X86_VSTEPS_TAC EXEC (28--28) THEN REABBREV_TAC `sx2 = read YMM1 s28` THEN
  si2mk "/tmp/si2_s28.txt" "s28 done" THEN
  VAL_INT64_TAC `acc1:num` THEN
  X86_STEPS_KEEPEV_TAC EXEC (29--29) THEN
  (fun g -> (let oc=open_out "/tmp/si2_a.txt" in output_string oc "SI2 reached s29 (store done)"; close_out oc); ALL_TAC g) THEN
  SUBGOAL_THEN `sx2:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf2:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx2def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx2:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx2def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (fun g -> (let oc=open_out "/tmp/si2_b.txt" in output_string oc "sx2 subgoal done"; close_out oc); ALL_TAC g) THEN
  (SUBGOAL_THEN maskbit_tgt_2 ASSUME_TAC THENL [MASKBIT_TGT_2_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_2 ASSUME_TAC THENL [PF_PROOF_2; ALL_TAC]) THEN
  ACC1_IDENT_TAC THEN
  (fun g -> (let oc=open_out "/tmp/si2_c.txt" in output_string oc "maskbit/pf/acc1 done; entering store-fold"; close_out oc); ALL_TAC g) THEN
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
  X86_STEPS_KEEPEV_TAC EXEC (30--33) THEN
  SI2_MG_TAC THEN SI2_RESOLVE_MS;;
