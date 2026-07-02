(* Wiring CLEAN_BODY into MLDSA_REJ_UNIFORM_ETA4_CORRECT.
   body_lemma_tm = the loop body obligation (YMM2/3/4-strengthened invariant + COND postcond
   `if i+1<N then pc+52 else pc+314`). CONTINUE_TAC discharges the i+1<N branch via CLEAN_BODY +
   ENSURES_FRAME_SUBSUMED (CLEAN_BODY's frame [ZMM0;1;5;6] subsumed by the loop's [ZMM0..6]).
   The exit branch (i+1=N) is OPEN — see notes: clean_body's hyp niblen(16(i+1))<=248 is false at
   i+1=N (WOP exit), so CLEAN_BODY doesn't apply; the exit iteration needs its own proof
   (same SIMD processing, but ending with the loop guard TAKEN to pc+314; store/RAX bounds hold
   via NIBLEN_BOUND_FROM_WOP niblen(16N)<=280 < 2^32). *)
let CFRAME = `MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,, MAYCHANGE [ZMM0; ZMM1; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(res,1024)]`;;
let CONTINUE_TAC : tactic =
  SUBGOAL_THEN `(if i + 1 < N then pc + 52 else pc + 314) = pc + 52` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`i:num`;`stackpointer:int64`] MLDSA_REJUNIFORM_ETA4_CLEAN_BODY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_X_ASSUM(fun th -> if is_forall(concl th) then MP_TAC(SPEC `i+1` th) else NO_TAC) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);
    DISCH_TAC] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC CFRAME THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC;
    FIRST_X_ASSUM ACCEPT_TAC];;
