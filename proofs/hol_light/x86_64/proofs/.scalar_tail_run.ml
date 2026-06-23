(* ========================================================================= *)
(* SCALAR_TAIL_RUN: byte-loop-to-exit by strong induction on byte-budget d.   *)
(* Needs hyp LENGTH(REJ(SUB(0,p)))<=256 (the SIMD loop exits with outlen<=256, *)
(* so count-exit gives outlen=256 exactly = cap length). Load after main +     *)
(* .scalar_tail_lemmas + .scalar_tail_build + .scalar_body_lemma.              *)
(*                                                                            *)
(* STATUS: FULLY PROVEN cheat-free (2026-06-23). Induction on d; 4-way split   *)
(* per step: count-exit (outlen>=256), offset-exit (p=272), mid-byte exit      *)
(* (outlen=255 /\ low<9), clean-recursive (body trip then IH at p+1 via        *)
(* ENSURES_SEQUENCE_TAC + ENSURES_PRECONDITION/POSTCONDITION_THM).             *)
(* ========================================================================= *)

(* LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc) = 406 (tmc has length 407). *)
let LENGTH_BUTLAST_GEN = prove
 (`!l:A list. ~(l = []) ==> LENGTH l = LENGTH(BUTLAST l) + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:A list` APPEND_BUTLAST_LAST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

let LENGTH_BUTLAST_TMC = prove
 (`LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc) = 406`,
  MP_TAC(ISPEC `mldsa_rej_uniform_eta4_tmc` LENGTH_BUTLAST_GEN) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SCALAR_TAIL_RUN = prove
 (`!d res buf table (inlist:byte list) pc (p:num) stackpointer.
        272 - p <= d /\
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        p <= 272 /\
        LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 256
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 318) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)) /\
                  read RCX s = word p /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list))) s =
                    num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)))
             (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                   read RAX s = word(LENGTH outlist) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  INDUCT_TAC THENL
   [(* ================= BASE CASE: d = 0 => p = 272 ================= *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `p = 272` SUBST_ALL_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`272 - p <= 0` || c=`p <= 272`))) THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_272) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`]) THEN
    REWRITE_TAC[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`] THEN
    ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256` THENL
     [(* --- BASE COUNT-EXIT: outlen = 256 --- *)
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[];
      (* --- BASE OFFSET-EXIT: outlen < 256, p = 272 --- *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) < 256` ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) <= 256` || c=`~(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256)`))) THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `&(val(word_zx(word 272:int64):int32)):int - &272 = &(val(word_sub(word_zx(word 272:int64):int32) (word 272):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[]];
    (* ================= STEP CASE: SUC d ================= *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `256 <= LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)` THENL
     [(* --- STEP COUNT-EXIT: outlen >= 256 (=256 by invariant) --- *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`inlist:byte list`; `p:num`] SUB_LIST_256_PREFIX_GE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)`;
                  ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`; LENGTH_BUTLAST_TMC] THEN
      ASM_REWRITE_TAC[];
      (* --- not count-exit: outlen < 256 --- *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `p = 272` THENL
       [(* --- STEP OFFSET-EXIT: p = 272 --- *)
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `p = 272`)) THEN
        MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_272) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`]) THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`] THEN
        MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
        ENSURES_INIT_TAC "s0" THEN
        SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        SUBGOAL_THEN `&(val(word_zx(word 272:int64):int32)):int - &272 = &(val(word_sub(word_zx(word 272:int64):int32) (word 272):int32))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
        X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[];
        (* --- p < 272 --- *)
        SUBGOAL_THEN `p < 272` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 9` THENL
         [(* --- STEP MID-BYTE EXIT: outlen=255, low<9 (accept low pushes to 256) --- *)
          FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj(concl th) && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))(concl th))) THEN
          SUBGOAL_THEN `256 <= LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list)` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN
            ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `?rest. REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list =
             APPEND (APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]) rest`
           STRIP_ASSUME_TAC THENL
           [ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
             [EXISTS_TAC `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
              EXISTS_TAC `[]:int32 list` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL]]; ALL_TAC] THEN
          MP_TAC(SPECL [`inlist:byte list`; `p+1`] SUB_LIST_256_PREFIX_GE) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
          SUBGOAL_THEN `LENGTH(APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]:int32 list) = 256` ASSUME_TAC THENL
           [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
               APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                      [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]` ASSUME_TAC THENL
           [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            W(fun (asl,gl) -> let lt = rhs gl in
               MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (mk_comb(`SUB_LIST(0,256):(int32)list->(int32)list`, lt)) THEN
               CONJ_TAC THENL
                [MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[LE_REFL];
                 MATCH_MP_TAC SUB_LIST_256_LE THEN ASM_REWRITE_TAC[LE_REFL]]); ALL_TAC] THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 4:int16) (word (val (EL p (inlist:byte list)) MOD 16))):int32]`] THEN
          REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255`] THEN
          ENSURES_INIT_TAC "s0" THEN
          MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `272`] READ_1BYTE_EL) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          SUBGOAL_THEN `~(&(val(word_zx(word 255:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 255:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &272 = &(val(word_sub(word_zx(word p:int64):int32) (word 272):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--8) THEN
          SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 272`) THEN ARITH_TAC; ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                                      ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                                      R10_NIBBLE_VAL]) THEN
          DISCARD_OLDSTATE_TAC "s8" THEN
          SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--14) THEN
          DISCARD_OLDSTATE_TAC "s14" THEN
          SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (15--16) THEN
          ENSURES_FINAL_STATE_TAC THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 4:int16) (word (val (EL p (inlist:byte list)) MOD 16))):int32]`] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[ASSUME `LENGTH(APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]:int32 list) = 256`] THEN
          REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
          (* memory fold: bytes(res,4*256) = APPEND prefix [lo] *)
          SUBGOAL_THEN `4 * 256 = 4 * 255 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s16:x86state`;
             `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
             `4*255`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            SUBGOAL_THEN `word(4 * 255):int64 = word 1020` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s16:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
               then ASSUME_TAC(REWRITE_RULE[MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c) && can(find_term(fun t->t=`s16:x86state`))c
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s16:x86state` `word_add res (word 1020):int64`];
          (* --- STEP CLEAN-RECURSIVE: body trip then IH at p+1 --- *)
          SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) <= 256` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN
            DISCH_THEN SUBST1_TAC THEN
            REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th -> let c=concl th in
               c = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ||
               c = `~(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 9)`))) THEN
            REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ARITH_TAC; ALL_TAC] THEN
          (* body lemma instance at (p, outlen(p)) *)
          MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;
             `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)`;`stackpointer:int64`] SCALAR_TAIL_BODY) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(fun body_th ->
            let bodyQ = rand(rator(concl body_th)) in
            ENSURES_SEQUENCE_TAC `pc + 318` bodyQ THEN
            CONJ_TAC THENL
             [(* leg1: P -> bodyQ via the body lemma (precond/postcond weaken) *)
              MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
              EXISTS_TAC (rand(rator(concl body_th))) THEN CONJ_TAC THENL
               [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
                MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
                EXISTS_TAC (rand(rator(rator(concl body_th)))) THEN CONJ_TAC THENL
                 [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
                  ACCEPT_TAC body_th]];
              (* leg2: bodyQ -> R = IH at p+1 *)
              ALL_TAC]) THEN
          (* leg2: weaken pre to IH's expanded pre, then apply IH@(p+1) *)
          FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
            (let ih_inst = SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p+1`;`stackpointer:int64`] ih in
             let ih_pre = rand(rator(rator(snd(dest_imp(concl ih_inst))))) in
             MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC ih_pre THEN CONJ_TAC THENL
              [GEN_TAC THEN BETA_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
               MP_TAC ih_inst THEN ANTS_TAC THENL
                [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]])
            else NO_TAC)]]]]);;
