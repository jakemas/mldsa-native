let SI2_RESOLVE : tactic =
  X86_STEPS_TAC EXEC (34--35) THEN
  SUBGOAL_THEN `read RIP s35 = word (pc + 215):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let blk1 = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` &&
                (match off with Comb(Comb(Const("+",_),Comb(Comb(Const("*",_),_),_)),_)->true|_->false) | _->false) with _->false) | _ -> false) asms in
      ignore blk1;
      let pop_len2 = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asms in
      let rax_red0 = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asms in
      let ja = find (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asms in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 215`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[pop_len2] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* fold RAX read clean for downstream (sub-iter 3) *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let pl = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asms in
    let rr = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asms in
    RULE_ASSUM_TAC(REWRITE_RULE[pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[rr]));;
