  W(fun (asl,w) ->
      let m8raw = find (fun th -> is_eq(concl th) && lhand(concl th)=`mask8:int64` &&
          can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) (map snd asl) in
      let m8 = SYM m8raw in
      let mtgt_imp = prove(mk_imp(concl m8, maskbit_tgt), DISCH_TAC THEN MASKBIT_PF_TAC) in
      ASSUME_TAC (MP mtgt_imp m8)) THEN
