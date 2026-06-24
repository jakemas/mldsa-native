(* ========================================================================= *)
(* EXIT_BLOCK: the single remaining goal after CORRECT_SCAFFOLD_TAC.           *)
(* Splits on niblen(SUB(0,16N))<=248:                                          *)
(*  - OFFSET arm (<=248): forces 16N=272 (N=17), apply EXIT_OFFSET.            *)
(*  - MID-EXIT arm (>248): a cmp eax,248;ja mid-guard fires inside the i=N-1    *)
(*    block at the first sub-iter offset p where niblen(p)>248 -> pc+318@p,     *)
(*    then SCALAR_TAIL_AT_P@p.                                                  *)
(* Load after: full CLEAN_BODY chain, CLEAN_BLOCK, .exit_offset (EXIT_OFFSET),  *)
(* .subiter_bridge_lemmas, .scalar_tail_run (AT_P), .correct_scaffold.          *)
(* ========================================================================= *)

(* let-free EXIT_OFFSET so its post matches the scaffold goal post verbatim. *)
let EXIT_OFFSET_NOLET = CONV_RULE(TOP_DEPTH_CONV let_CONV) EXIT_OFFSET;;

(* OFFSET arm: niblen(16N)<=248 in assumptions -> 16N=272 -> EXIT_OFFSET. VALIDATED. *)
let OFFSET_ARM_TAC : tactic =
  SUBGOAL_THEN `16 * N = 272` ASSUME_TAC THENL
   [SUBGOAL_THEN `256 < 16 * N` ASSUME_TAC THENL
     [UNDISCH_TAC `256 < 16 * N \/ 248 < LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * N) inlist):int16 list)` THEN
      REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
      UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `N = 17` (fun th -> REWRITE_TAC[th] THEN CONV_TAC NUM_REDUCE_CONV) THEN
    UNDISCH_TAC `16 * (N-1) <= 256` THEN UNDISCH_TAC `256 < 16 * N` THEN
    UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC EXIT_OFFSET_NOLET THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
  SUBST1_TAC(ASSUME `16 * N = 272`) THEN REWRITE_TAC[];;

(* MID-EXIT arm: still under construction. *)
