let SI1_FOLD : tactic =
  SUBGOAL_THEN
   `!j. j < 8 ==>
      word_subword (word_subword (f0sub:int256) (0,128):int128) (8*j,8):byte =
      word_sub (word 4) (word(EL j [val(word_subword (chunk0:int128) (0,8):byte) MOD 16;
         val(word_subword chunk0 (0,8):byte) DIV 16; val(word_subword chunk0 (8,8):byte) MOD 16;
         val(word_subword chunk0 (8,8):byte) DIV 16; val(word_subword chunk0 (16,8):byte) MOD 16;
         val(word_subword chunk0 (16,8):byte) DIV 16; val(word_subword chunk0 (24,8):byte) MOD 16;
         val(word_subword chunk0 (24,8):byte) DIV 16]):byte)`
   (fun bg ->
    SUBGOAL_THEN maskbit_tgt (fun mthm ->
     SUBGOAL_THEN pf_target (fun pfth ->
      W(fun (asl,w) ->
        let asms = map snd asl in
        (* the store at s23 already has RHS = usimd8 form (stepA's sx1=usimd8 was auto-applied). *)
        let storef = find (fun th -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false))(concl th) &&
            can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))(concl th) &&
            (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s23",_))),_)->true|_->false)) asms in
        (* rewrite pshuf1 -> usimd16/TABLE form (pfth). NO WORD_ZX_TRIVIAL (it would wrongly
           collapse the control's double-zx). Use g := the double-zx form to match the store. *)
        let store_full = REWRITE_RULE[pfth] storef in
        let g = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
        let m = `word (val (mask8:int64) MOD 256):byte` in
        let pc = ISPECL [`word_add res (word (4 * outlen0)):int64`; `s23:x86state`; g; m; `LENGTH(ACC_IDX (word (val (mask8:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
        let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
        let spec = ISPECL [g; m; `word_subword (chunk0:int128) (0,8):byte`; `word_subword (chunk0:int128) (8,8):byte`; `word_subword (chunk0:int128) (16,8):byte`; `word_subword (chunk0:int128) (24,8):byte`] SUBITER_STORE_SPEC in
        (* spec's gather hyp (with double-zx g) = bg after collapsing identity word_zx; build gthm. *)
        (let oc=open_out "/tmp/specform.txt" in output_string oc (string_of_term(lhand(concl spec))); close_out oc);
        let gather_hyp = List.nth (conjuncts(lhand(concl spec))) 1 in
        (* gather_hyp = bg modulo word_zx(word_zx ·)=· (identity); EQ_MP the rewrite. *)
        let gthm = EQ_MP (SYM(REWRITE_CONV[WORD_ZX_TRIVIAL] gather_hyp)) bg in
        let specres = MP spec (CONJ mthm gthm) in
        let rej_store = REWRITE_RULE[specres] res_th0 in
        (* ---- SUB-ITER 1 MEMORY FOLD (2026-06-13): fold rej_store (block store at res+4*outlen0)
           with the prefix store into the clean advanced prefix store for SUB_LIST(0,16i+4).
           Done HERE (inner W) so rej_store + mthm are OCaml values in scope (mthm is threaded,
           not assumed, so it can't be re-found). Validated forward inference (/tmp/subiter1_clean.txt).
           Uses LEN_RECONCILE + SUBITER_BLOCK_BYTES + SUBITER_FOLD_STEP + SUB_LIST_SPLIT. ---- *)
        let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
        let blk = `[word_subword (chunk0:int128) (0,8); word_subword chunk0 (8,8); word_subword chunk0 (16,8); word_subword chunk0 (24,8)]:byte list` in
        let prefixbytes = `SUB_LIST(0,16*i) (inlist:byte list)` in
        (* prefix store: read(memory:>bytes(res,4*outlen0)) s23 = nwl(REJ(SUB_LIST(0,16i))).
           identify by: read-eq at s23, RHS has num_of_wordlist+SUB_LIST, address mentions outlen0 (not ACC_IDX). *)
        let prefix_store = find (fun th ->
             (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s23",_))),_) -> true | _ -> false) &&
             hasC "num_of_wordlist" th && hasC "SUB_LIST" th &&
             can(find_term(fun u->u=`res:int64`))(lhand(concl th)) &&
             can(find_term(fun u->u=`outlen0:num`))(lhand(concl th)) &&
             not(hasC "ACC_IDX" th)) asms in
        let len_eq = find (fun th -> match concl th with
             Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asms in
        let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
             (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
        let leninl = find (fun th -> match concl th with
             Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
        let i116 = find (fun th -> match concl th with
             Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
        let lenle = REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1) <= 256 ==> 16*i+16 <= 272`) i116) in
        let lr = MP (ISPECL [m; `chunk0:int128`] LEN_RECONCILE) mthm in
        let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES) (CONJ lenle blk16) in
        let blk_bytes = CONJUNCT1 bb in
        let rej_store2 = REWRITE_RULE[SYM len_eq] rej_store in
        let prefix_store2 = REWRITE_RULE[SYM len_eq] prefix_store in
        let fold = MP (ISPECL [`res:int64`;`s23:x86state`;m;blk;prefixbytes] SUBITER_FOLD_STEP)
                      (CONJ lr (CONJ prefix_store2 rej_store2)) in
        let split0 = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i`;`4`;`0`] SUB_LIST_SPLIT) in
        let clean = REWRITE_RULE[GSYM blk_bytes; GSYM split0] fold in
        (let oc = open_out "/tmp/fold_state.txt" in
         output_string oc ("SUB-ITER 1 FOLD DONE (inner W). clean store =\n"^string_of_term(concl clean)^"\n");
         close_out oc);
        ASSUME_TAC clean))
     THENL
      [ALL_TAC
       ;
       W(fun (asl,w) ->
         let pdef = find (fun th -> is_eq(concl th) && rand(concl th)=`pshuf1:int256` && can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
         let teq = find (fun th -> is_eq(concl th) && lhand(concl th)=`tab1:int256` && can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)) (map snd asl) in
         SUBST1_TAC(SYM pdef) THEN REWRITE_TAC[teq] THEN
         REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
         SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH] THEN
         CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ZX_TRIVIAL; VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV)])
    THENL [ALL_TAC; MASKBIT_PF_TAC])
   THENL
    [ALL_TAC;
     (* bare gather forall proof: JOIN extract over f0sub def *)
     W(fun (asl,w) ->
       let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
       REPEAT STRIP_TAC THEN
       FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
         (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
       REWRITE_TAC[f0d] THEN
       REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
         CONV_TAC NUM_REDUCE_CONV)) THEN
       REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)];;
