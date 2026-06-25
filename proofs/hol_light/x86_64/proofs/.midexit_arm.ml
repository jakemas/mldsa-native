(* MIDEXIT_ARM_TAC: closes the scaffold's MID-EXIT arm (the goal after CORRECT_SCAFFOLD_TAC +
   ASM_CASES niblen(16N)<=248, FALSE branch). Pre @ pc+52/pos16(N-1), niblen(16(N-1))<=248,
   niblen(16N)>248. Case-splits on the first crossover p in {16(N-1)+4,+8,+12,16N} and dispatches
   MID_EXIT_SUBITER{1,2,3}@(N-1) / MID_EXIT_CASE4@(N-1), then SCALAR_TAIL_AT_P@p -> pc+402.
   Load after the 4 MID_EXIT lemmas, SCALAR_TAIL_AT_P, OUTLEN0_LE_256_FROM_SUBITER. *)

let AT_P_NOLET = CONV_RULE(TOP_DEPTH_CONV let_CONV) MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P;;

(* dispatch one crossover case: midthm @ i:=N-1 reaches pc+314@pexpr; prevbound = niblen(pexpr-4)<=248
   (in context) used to derive niblen(pexpr)<=256; then SCALAR_TAIL_AT_P@pexpr. *)
let MIDEXIT_DISPATCH (midthm:thm) (pexpr:term) (prevpos:term) : tactic =
  let qpost = vsubst [`N-1`,`i:num`] (rand(rator(snd(dest_imp(snd(strip_forall(concl midthm))))))) in
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC qpost THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* leg1: MID_EXIT lemma @ N-1 *)
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N-1`;`stackpointer:int64`] midthm) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); DISCH_THEN ACCEPT_TAC];
    (* leg2: niblen(pexpr)<=256 then SCALAR_TAIL_AT_P@pexpr *)
    SUBGOAL_THEN (mk_comb(mk_comb(`(<=):num->num->bool`,
        mk_comb(`LENGTH:(int32)list->num`, mk_comb(`REJ_SAMPLE_ETA4_BYTES:byte list->int32 list`,
          mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,mk_pair(`0`,pexpr)),`inlist:byte list`)))), `256`)) ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(pexpr, mk_binop `(+):num->num->num` prevpos `4`)) SUBST1_TAC THENL
       [UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `16 * N <= 272` THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC OUTLEN0_LE_256_FROM_SUBITER THEN CONJ_TAC THENL
       [UNDISCH_TAC `16 * N <= 272` THEN UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MATCH_MP_TAC AT_P_NOLET THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];;

let MIDEXIT_ARM_TAC : tactic =
  (* setup facts (idempotent if already present) *)
  SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,16 * N) inlist):int32 list) <= 248)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * N <= 272` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (N-1) <= 256` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * ((N-1)+1) <= 272` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * N <= 272` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  (* crossover case-split *)
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+4) inlist):int32 list) <= 248` THENL
   [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+8) inlist):int32 list) <= 248` THENL
     [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+12) inlist):int32 list) <= 248` THENL
       [(* all 3 internal <=248 -> case-4, p = 16*((N-1)+1) *)
        SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*((N-1)+1)) inlist):int32 list)` ASSUME_TAC THENL
         [SUBGOAL_THEN `16*((N-1)+1) = 16*N` SUBST1_TAC THENL
           [UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MIDEXIT_DISPATCH MID_EXIT_CASE4 `16*((N-1)+1)` `16*(N-1)+12`;
        (* niblen(16(N-1)+12)>248 -> case-3, p=16(N-1)+12 *)
        MIDEXIT_DISPATCH MID_EXIT_SUBITER3 `16*(N-1)+12` `16*(N-1)+8`];
      (* niblen(16(N-1)+8)>248 -> case-2, p=16(N-1)+8 *)
      MIDEXIT_DISPATCH MID_EXIT_SUBITER2 `16*(N-1)+8` `16*(N-1)+4`];
    (* niblen(16(N-1)+4)>248 -> case-1, p=16(N-1)+4 *)
    MIDEXIT_DISPATCH MID_EXIT_SUBITER1 `16*(N-1)+4` `16*(N-1)`];;
