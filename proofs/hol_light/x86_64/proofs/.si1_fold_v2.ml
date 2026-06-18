(* SI1_FOLD_V2: sub-iter-1 store recombination, cheat-free. gather forall + maskbit_tgt are
   ALREADY ASSUMEd by PREFIX_G_FULL_TAC, so fetch them from asl (no SUBGOAL_THEN). Only
   pf_target is a real subgoal, discharged by PF_PROOF (genuine table-load bridge). *)
let SI1_FOLD_V2 : tactic =
  SUBGOAL_THEN pf_target (fun pfth ->
    W(fun (asl,w) ->
      let asms = map snd asl in
      let bg = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))c) asms in
      let mthm = find (fun th -> concl th = maskbit_tgt) asms in
      let storef = find (fun th -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false))(concl th) &&
          can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))(concl th) &&
          (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s23",_))),_)->true|_->false)) asms in
      let store_full = REWRITE_RULE[pfth] storef in
      let g = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
      let m = `word (val (mask8:int64) MOD 256):byte` in
      let pc = ISPECL [`word_add res (word (4 * outlen0)):int64`; `s23:x86state`; g; m; `LENGTH(ACC_IDX (word (val (mask8:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
      let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
      let spec = ISPECL [g; m; `word_subword (chunk0:int128) (0,8):byte`; `word_subword (chunk0:int128) (8,8):byte`; `word_subword (chunk0:int128) (16,8):byte`; `word_subword (chunk0:int128) (24,8):byte`] SUBITER_STORE_SPEC in
      let gather_hyp = List.nth (conjuncts(lhand(concl spec))) 1 in
      let gthm = EQ_MP (SYM(REWRITE_CONV[WORD_ZX_TRIVIAL] gather_hyp)) bg in
      let specres = MP spec (CONJ mthm gthm) in
      let rej_store = REWRITE_RULE[specres] res_th0 in
      let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
      let blk = `[word_subword (chunk0:int128) (0,8); word_subword chunk0 (8,8); word_subword chunk0 (16,8); word_subword chunk0 (24,8)]:byte list` in
      let prefixbytes = `SUB_LIST(0,16*i) (inlist:byte list)` in
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
      ASSUME_TAC clean))
  THENL [PF_PROOF; ALL_TAC];;
