(* EXIT_OFFSET development — offset arm of the exit block. *)
let exit_offset_tm = `
  !res buf table (inlist:byte list) pc N stackpointer.
       LENGTH inlist = 272 /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val res,1024) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val buf, 272) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val table,2048) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
       16 * N = 272 /\
       LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*N) inlist):int16 list) <= 248
       ==> ensures x86
            (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                 read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
                 read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                 read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                 read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                 read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                 read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
                 read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
                 read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list)) /\
                 read RCX s = word(16*(N-1)) /\
                 read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list))) s =
                   num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist)))
            (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                 (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                  read RAX s = word(LENGTH outlist) /\
                  read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
            (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
             MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(res,1024)])`;;

(* Q318: post-head-guard state at pc+314, pos=16N. *)
let q318 = `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
      read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist))`;;

let q56 = `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
      read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
      read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
      read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist))`;;

let EXIT_OFFSET = prove(exit_offset_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*N) inlist):int16 list) <= 248` then ACCEPT_TAC th else NO_TAC); ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q318 THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [(* leg1: pc+52 -> Q318 : CLEAN_BLOCK@(N-1) [pc+52 pos16(N-1) -> pc+52 pos16N] then
       head guard cmp eax,248 (not taken, niblen(16N)<=248) + cmp ecx,256 (TAKEN, 16N=272>256) -> pc+314. *)
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q56 THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [(* leg1a: CLEAN_BLOCK@(N-1), post pos=16N = q56 (modulo N-1+1 -> N). VALIDATED in-session.
         Pre/post predicates match q56 exactly; only the MAYCHANGE frame differs
         (CLEAN_BLOCK has ZMM0;1;5;6, cframe has ZMM0..6) -> frame subsumption. *)
      SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL [UNDISCH_TAC `16 * N = 272` THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`N-1`;`stackpointer:int64`] CLEAN_BLOCK) THEN
      SUBGOAL_THEN `N - 1 + 1 = N` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC;
      (* leg1b: q56 (pc+52 pos16N) -> Q318 via head guards. VALIDATED in-session.
         Guards stated in 272-form (16*N=272) because the stepper rewrites the flag
         predicates to 272-form, so the ja branch decision must match that form.
         cmp eax,248 (s1) not taken [niblen(272)<=248]; ja (s2); cmp ecx,256 (s3) TAKEN [272>256]; ja (s4)->pc+314. *)
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list) <= 248` ASSUME_TAC THENL
       [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
        SUBST1_TAC(ASSUME `16 * N = 272`) THEN REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32)):int - &248 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32) (word 248):int32))) \/ val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32) (word 248):int32) = 0` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_NOT_TAKEN_LE THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(~(&(val(word_zx(word(272):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(272):int64):int32) (word 256):int32))) \/ val(word_sub(word_zx(word(272):int64):int32) (word 256):int32) = 0)` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_TAKEN_GT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `16 * N = 272`]) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];
    (* leg2: Q318 -> pc+402 : SCALAR_TAIL_AT_P @ p=16N. Weaken precond to AT_P's pre. *)
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(concl(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`16*N`;`stackpointer:int64`] MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`16*N`;`stackpointer:int64`]
                   MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN
        (FIRST [FIRST_ASSUM ACCEPT_TAC;
                ASM_ARITH_TAC;
                (FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` then MP_TAC th else NO_TAC) THEN ARITH_TAC)]);
        DISCH_THEN ACCEPT_TAC]]]);;
