let PREFIX_G_TAC : tactic =
  REPEAT GEN_TAC THEN
  (ALL_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * i <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i + 1) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`;`272`;`inlist:byte list`;`i:num`;`s0:x86state`] SUB_LIST_16_BYTES_FROM_INT128) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i+1) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf (word(16*i)))) s0` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    TRANS_TAC LE_TRANS `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i+1)) inlist):int16 list)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)` THEN
  FIRST_ASSUM(fun th -> if concl th =
      `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) else NO_TAC) THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  VAL_INT64_TAC `outlen0:num` THEN
  X86_STEPS_TAC EXEC (1--2) THEN
  SUBGOAL_THEN `read RIP s2 = word(pc + 67):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 318`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (3--4) THEN
  SUBGOAL_THEN `read RIP s4 = word(pc + 79):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&256:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 318`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC EXEC (5--5) THEN
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `16*i <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(16*i):int64) = 16*i`; ARITH_RULE `1 * x = x`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read (memory :> bytes128 (word_add buf (word (16 * i)))) s4 = chunk0`]) THEN
  SUBGOAL_THEN `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s5`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256`]) THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM2 s5 =
    word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256`]) THEN
  SUBGOAL_THEN (mk_eq(`read YMM0 s8:int256`, F0NIB_CHUNK0)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s8`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s5";"s6";"s7"] THEN
  ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES) THEN
  ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES_HI) THEN
  ABBREV_TAC `fn:int256 = read YMM0 s8` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME(mk_eq(`fn:int256`, F0NIB_CHUNK0)))]) THEN
  X86_VSTEPS_TAC EXEC (9--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s8 = fn:int256`;
     ASSUME `read YMM4 s8 = word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256`]) THEN
  ABBREV_TAC `f1bnd:int256 = read YMM1 s9` THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s9 = fn:int256`;
     ASSUME `read YMM3 s9 = word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256`]) THEN
  ABBREV_TAC `f0sub:int256 = read YMM0 s10` THEN
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
  (* MASKBIT forall derived NOW (f1bnd word_join def still present): bit 7(f1bnd lane k) <=>
     EL k[chunk0 nibbles]<9. ASSUME it — survives the DROP below + downstream purges. Used by
     counter stage 3b. (Probe proves this SUBGOAL before its DROP, lines 216-237.) *)
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+16),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (64,8):byte) MOD 16; val(word_subword chunk0 (64,8):byte) DIV 16;
                  val(word_subword chunk0 (72,8):byte) MOD 16; val(word_subword chunk0 (72,8):byte) DIV 16;
                  val(word_subword chunk0 (80,8):byte) MOD 16; val(word_subword chunk0 (80,8):byte) DIV 16;
                  val(word_subword chunk0 (88,8):byte) MOD 16; val(word_subword chunk0 (88,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+24),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (96,8):byte) MOD 16; val(word_subword chunk0 (96,8):byte) DIV 16;
                  val(word_subword chunk0 (104,8):byte) MOD 16; val(word_subword chunk0 (104,8):byte) DIV 16;
                  val(word_subword chunk0 (112,8):byte) MOD 16; val(word_subword chunk0 (112,8):byte) DIV 16;
                  val(word_subword chunk0 (120,8):byte) MOD 16; val(word_subword chunk0 (120,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp2 = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+8),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (32,8):byte) MOD 16; val(word_subword chunk0 (32,8):byte) DIV 16;
                  val(word_subword chunk0 (40,8):byte) MOD 16; val(word_subword chunk0 (40,8):byte) DIV 16;
                  val(word_subword chunk0 (48,8):byte) MOD 16; val(word_subword chunk0 (48,8):byte) DIV 16;
                  val(word_subword chunk0 (56,8):byte) MOD 16; val(word_subword chunk0 (56,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp2 f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      (* prove `f1bnd = wj ==> (!k...)` as a CLOSED implication (f1d discharged as antecedent,
         so the result has NO extra hyps), then MP with f1d. The DISCH'd eq is used to rewrite. *)
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*k,8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (0,8):byte) MOD 16; val(word_subword chunk0 (0,8):byte) DIV 16;
                  val(word_subword chunk0 (8,8):byte) MOD 16; val(word_subword chunk0 (8,8):byte) DIV 16;
                  val(word_subword chunk0 (16,8):byte) MOD 16; val(word_subword chunk0 (16,8):byte) DIV 16;
                  val(word_subword chunk0 (24,8):byte) MOD 16; val(word_subword chunk0 (24,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  (fun g -> (let oc=open_out "/tmp/cs_mb.txt" in output_string oc "early maskbit assumed"; close_out oc); ALL_TAC g) THEN
  (* DROP f0sub/f1bnd word_join defs BEFORE vpmovmskb (s11) — mirrors the probe (clean_body_probe.ml
     lines 243-245). This keeps R8/R9's vpmovmskb+popcount over the OPAQUE `f1bnd` var (via the
     `read YMM1 s10 = f1bnd` fold) instead of the expanded word_join, so stage d's popeq / low8 /
     BOOL_CASES (over `word_subword f1bnd (8k,8)`) match the popcount term. Without this, R9 s21 =
     popcount(...word_join expanded...) and stage d leaves unsolved goals. *)
  REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && (lhand(concl th) = `f0sub:int256` || lhand(concl th) = `f1bnd:int256`)
     then ALL_TAC else failwith "keep")) THEN
  (* ---- STEP s11-s17 FIRST (vpmovmskb, vextracti128, movzbl R10 capture, vmovq, vpshufb,
     vpmovsxbd, vmovdqu store), keeping f0sub/f1bnd defs. The gather/mask SUBGOALs are proven
     AFTER stepping: their `EL j [...]`-shaped assumptions confuse X86_VSTEPS' simulator
     (vextracti128 at s12 fails with "mk_comb: types do not agree" if they're in context). ---- *)
  X86_VSTEPS_TAC EXEC (11--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM1 s10 = f1bnd:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s10"] THEN
  X86_VSTEPS_TAC EXEC (12--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s11 = f0sub:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s11"] THEN
  REABBREV_TAC `mask8 = read R8 s12` THEN
  X86_VERBOSE_STEP_TAC EXEC "s13" THEN
  MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s12 = mask8:int64`]) THEN
  X86_VSTEPS_TAC EXEC (14--14) THEN REABBREV_TAC `tab1 = read YMM6 s14` THEN
  X86_VSTEPS_TAC EXEC (15--15) THEN REABBREV_TAC `pshuf1 = read YMM6 s15` THEN
  PURGE_STALE_STATES_TAC ["s14"] THEN
  X86_VSTEPS_TAC EXEC (16--16) THEN REABBREV_TAC `sx1 = read YMM1 s16` THEN
  (* stepA: establish sx1 = usimd8 word_sx (word_zx(word_zx pshuf1)) (the vpmovsxbd lane form). *)
  SUBGOAL_THEN `sx1:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf1:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx1def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx1:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx1def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  PURGE_STALE_STATES_TAC ["s15"] THEN
  X86_STEPS_TAC EXEC (17--17) THEN
  PURGE_STALE_STATES_TAC ["s16"] THEN
  (fun g -> (let oc=open_out "/tmp/cs_s17.txt" in output_string oc "reached s17 (store done)"; close_out oc); ALL_TAC g) THEN
  X86_STEPS_TAC EXEC (18--21) THEN
  (fun g -> (let oc=open_out "/tmp/cs_c1821.txt" in output_string oc "counters 18-21 done"; close_out oc); ALL_TAC g) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 272` THEN
    UNDISCH_TAC `16 * i <= 256` THEN ARITH_TAC; STRIP_TAC] THEN
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM m8def])) THEN
  (* === REORDERED branch resolution (NO RULE_ASSUM over s21 state) === *)
  W(fun (asl,w) ->
    (* 1. popeq: word_popcount(word_zx^3(word(val mask8 MOD 256))) = bitsum8(low8 of f1bnd) *)
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s21",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    (* 2. bitsum8 = LENGTH(REJ_NIBBLES block0) via maskbit forall + block byte facts *)
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c) asl) in
    let mb_tm = concl maskbit in
    let mb_assumed = ASSUME mb_tm in
    let mbits = map (fun k -> let th=SPEC(mk_small_numeral k) mb_assumed in
         CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    (* combined: word_popcount(...) = LENGTH(REJ_NIBBLES block0) *)
    let pop_len = TRANS popeq bsum in
    (* 3. bound: outlen0 + LENGTH(REJ_NIBBLES block0) <= 248 *)
    let leninl = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asl in
    let i116 = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asl in
    let nible = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA4",_),_))),_) -> true | _ -> false) asl in
    let len_eq = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asl in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=256 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`)
                    (snd i116)) (snd leninl) in
    let bnd0 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_1) (CONJ a1 (snd nible)) in
    let bnd = REWRITE_RULE[snd len_eq] bnd0 in  (* outlen0 + LENGTH(REJ_NIBBLES block0) <= 248 *)
    (* 4. RAX collapse: word_zx(word_add(word_zx(word outlen0))(word_zx(word_zx(word popcount)))) = word(outlen0+block0len) *)
    let block0len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in  (* word_zx(...word outlen0...word block0len...) = word(outlen0+block0len) *)
    (* but RAX has popcount, not block0len; rewrite popcount->block0len first via pop_len *)
    let rax_red = REWRITE_RULE[pop_len] (GSYM(REWRITE_RULE[GSYM pop_len] (SYM rax_red0))) in
    (* JA_NOT_TAKEN: outlen0+block0len <= 248 *)
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `outlen0:num` block0len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    (let oc=open_out "/tmp/reorder_facts.txt" in
     output_string oc ("pop_len: "^string_of_term(concl pop_len)^"\n\nrax_red0: "^string_of_term(concl rax_red0)^
       "\n\nja: "^string_of_term(concl ja)^"\n\nbnd: "^string_of_term(concl bnd)^"\n"); close_out oc);
    (* stash these as assumptions for the step *)
    ASSUME_TAC pop_len THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (22--23) THEN
  (* resolve the ja branch: RIP s23 = pc+167 (fall through to sub-iter 2) *)
  SUBGOAL_THEN `read RIP s23 = word (pc + 167):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th)) asl in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 167`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* fold RAX read clean using the assumed pop_len + rax_red0 (now in asl) *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr])) THEN
  ALL_TAC);;
