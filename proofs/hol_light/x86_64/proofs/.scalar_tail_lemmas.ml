(* Foundational spec lemmas for the SCALAR_TAIL proof (pc+314 byte-at-a-time loop).
   Each scalar iteration consumes 1 input byte = 2 nibbles (low then high), accepting each if <9,
   matching REJ_SAMPLE_ETA4_BYTES_1. These give the per-byte step of the loop invariant. *)

let SUB_LIST_1_EL = prove
 (`!l:byte list. !p. p < LENGTH l ==> SUB_LIST(p,1) l = [EL p l]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ARITH_RULE `1 = SUC 0`; SUB_LIST_CLAUSES; SUB_LIST; EL; HD] THEN
    REWRITE_TAC[ONE; SUB_LIST_CLAUSES];
    DISCH_TAC THEN
    SUBGOAL_THEN `?q. p = SUC q` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [EXISTS_TAC `p - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; EL; TL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let SUB_LIST_STEP_1 = prove
 (`!l:byte list. !p. p < LENGTH l ==> SUB_LIST(0,p+1) l = APPEND (SUB_LIST(0,p) l) [EL p l]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`l:byte list`;`p:num`;`1`;`0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_1_EL]);;

let REJ_SAMPLE_STEP_1 = prove
 (`!inlist:byte list. !p. p < LENGTH inlist ==>
     REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) =
     APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)) (REJ_SAMPLE_ETA4_BYTES [EL p inlist])`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUB_LIST_STEP_1; REJ_SAMPLE_ETA4_BYTES_APPEND]);;

let LENGTH_REJ_SAMPLE_STEP_1 = prove
 (`!inlist:byte list. !p. p < LENGTH inlist ==>
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) +
     (if val(EL p inlist) MOD 16 < 9 then 1 else 0) + (if val(EL p inlist) DIV 16 < 9 then 1 else 0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REJ_SAMPLE_STEP_1; LENGTH_APPEND; LENGTH_REJ_SAMPLE_ETA4_BYTES_1] THEN ARITH_TAC);;
