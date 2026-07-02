  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let gather_imp = prove
       (mk_imp(concl f0d,
        `!j. j < 8 ==>
           word_subword (word_subword (f0sub:int256) (0,128):int128) (8*j,8):byte =
           word_sub (word 4) (word(EL j [val(word_subword (chunk0:int128) (0,8):byte) MOD 16;
              val(word_subword chunk0 (0,8):byte) DIV 16; val(word_subword chunk0 (8,8):byte) MOD 16;
              val(word_subword chunk0 (8,8):byte) DIV 16; val(word_subword chunk0 (16,8):byte) MOD 16;
              val(word_subword chunk0 (16,8):byte) DIV 16; val(word_subword chunk0 (24,8):byte) MOD 16;
              val(word_subword chunk0 (24,8):byte) DIV 16]):byte)`),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP gather_imp f0d)) THEN
