(* ========================================================================= *)
(* CORRECT scaffold (2026-06-23): the validated Phase-0/1/2 tactic chain that  *)
(* reduces MLDSA_REJ_UNIFORM_ETA4_CORRECT to a SINGLE remaining goal — the     *)
(* exit-block obligation `inv(N-1) @ pc+56 -> CORRECT-post @ pc+406`.           *)
(*                                                                            *)
(* Uses ENSURES_WHILE_UP_TAC (N-1) (pc+56)(pc+56) [NOT the old UP2-at-N which  *)
(* mis-handles mid-block exits]. Body blocks 0..N-2 are all clean, discharged  *)
(* by MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY (must be in scope — load .clean_body    *)
(* chain first). G0/G1/G2/G3 of the loop all close; only the exit obligation   *)
(* (the i=N-1 block stepped with per-guard branch analysis -> pc+318 at exit   *)
(* position p, then SCALAR_TAIL_AT_P -> pc+406) remains = the exit-block proof. *)
(*                                                                            *)
(* Prerequisites in session: main eta4 file; the full CLEAN_BODY chain (so     *)
(* MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY is proven); .scalar_tail_run.ml           *)
(* (SCALAR_TAIL_AT_P); .subiter_bridge_lemmas.ml. *)
(* ========================================================================= *)

(* The strengthened loop invariant (adds YMM2/3/4 broadcast constants). *)
let CORRECT_LOOPINV =
 `\i s. read RSP s = stackpointer /\
        read (memory :> bytes (buf, 272)) s = num_of_wordlist inlist /\
        read (memory :> bytes (table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
        read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
        read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
        read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
        read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
        read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
        read RCX s = word(16*i) /\
        read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s =
          num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist))`;;

(* Phase 0/1/2 scaffold. After this, ONE goal remains = the exit-block obligation. *)
let CORRECT_SCAFFOLD_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES; LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
  STRIP_TAC THEN GHOST_INTRO_TAC `stackpointer:int64` `read RSP` THEN
  (* Phase 1: WOP *)
  SUBGOAL_THEN `?i. 256 < 16 * i \/ 248 < LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * i) inlist):int16 list)` MP_TAC THENL
   [EXISTS_TAC `17:num` THEN ARITH_TAC; GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT] th)) THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  (* N=1 impossible: niblen(16)<=32<248 and 256<16 false *)
  ASM_CASES_TAC `N = 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[ARITH_RULE `~(256 < 16 * 1)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`; `16`] LENGTH_REJ_SAMPLE_ETA4_BYTES_SUB_LIST_BOUND) THEN
    ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `16 * 1 = 16`] THEN ARITH_TAC; ALL_TAC] THEN
  (* Phase 2: clean-block loop over N-1 iterations *)
  ENSURES_WHILE_UP_TAC `N - 1` `pc + 56` `pc + 56` CORRECT_LOOPINV THEN
  REPEAT CONJ_TAC THENL
   [(* G0 ~(N-1=0) *)
    REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->concl th=`~(N=0)`||concl th=`~(N=1)`))) THEN ARITH_TAC;
    (* G1 init pc -> pc+56 *)
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4;
                NIBBLES_OF_BYTES; FILTER; MAP; LENGTH; num_of_wordlist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN CONV_TAC WORD_REDUCE_CONV;
    (* G2 body: CLEAN_BODY @ i + frame subsumption *)
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`i:num`;`stackpointer:int64`] MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `i + 1 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i+1` o check(is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC;
    (* G3 back-edge: refl *)
    REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* G4 exit obligation -- LEFT OPEN for the exit-block proof *)
    ALL_TAC] THEN
  (* exit-block entry facts (hyp7 @ N-1) *)
  SUBGOAL_THEN `16 * (N-1) <= 256 /\ LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(N-1)) inlist):int16 list) <= 248` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N-1` o check(is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES]; ALL_TAC];;
(* Remaining after CORRECT_SCAFFOLD_TAC: the single exit-block goal at pc+56,
   pos=16(N-1), niblen<=248 -> CORRECT-post@pc+406. *)
