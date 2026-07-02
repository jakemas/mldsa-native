(* ========================================================================= *)
(* SCALAR_TAIL per-byte body lemma — full cheat-free proof.                    *)
(* One trip pc+314 -> pc+314 consuming input byte at position p, extending     *)
(* the output by REJ_SAMPLE_ETA4_BYTES[EL p inlist]. Entry generalized to      *)
(* arbitrary p. The ~(L=255 /\ low<9) hyp rules out the mid-byte exit (that    *)
(* case is the terminal segment, handled by the WOP wrapper, not this body).   *)
(* Loaded after main eta4 file + .scalar_tail_lemmas + .scalar_tail_build.     *)
(* Requires type_invention_error := true.                                      *)
(* ========================================================================= *)

(* Common RCX closer: word_zx(word_add(word_zx(word p))(word 1)):int64 = word(p+1) for p<272. *)
let RCX_INC_TAC =
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val(word_zx(word p:int64):int32) = p` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN MP_TAC(ASSUME `p<272`) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx(word_add (word_zx (word p:int64):int32) (word 1:int32)):int64) = p+1` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word_add (word_zx (word p:int64):int32) (word 1:int32)) = p + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_32] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ASSUME `p<272`) THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `val(word_add (word_zx (word p:int64):int32) (word 1:int32))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_ZX THEN REWRITE_TAC[DIMINDEX_32;DIMINDEX_64] THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ASSUME `p<272`) THEN ARITH_TAC];;

(* setup to s8: lands RIP=pc+343 with R10=word(val(EL p (inlist:byte list)) MOD 16), outlen0 abbreviated,
   LENGTH(REJ(SUB(0,p)))=outlen0 kept. *)
let SCALAR_BODY_SETUP =
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `272`] READ_1BYTE_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `L:num = outlen0` then SUBST_ALL_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `~(&(val(word_zx(word outlen0:int64):int32)):int - &256 = &(val(word_sub(word_zx(word outlen0:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &272 = &(val(word_sub(word_zx(word p:int64):int32) (word 272):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--8) THEN
  SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 272`) THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                              ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                              R10_NIBBLE_VAL]) THEN
  DISCARD_OLDSTATE_TAC "s8";;

(* prove read(bytes(addr,4)) sN = val(word_sx ...) from a spec-form bytes32 store hyp. *)
let STORE4_FROM_SPEC sN addrt =
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN REWRITE_TAC[VAL_WORD] THEN
  SUBGOAL_THEN (subst[sN,`s:x86state`;addrt,`a:int64`]
     `read (bytes (a:int64,4)) (read memory (s:x86state)) < 2 EXP dimindex(:32)`) ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_32] THEN
    MP_TAC(ISPECL[addrt;`4`;mk_comb(`read memory:x86state->int64->byte`,sN)] READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;;

let SCALAR_TAIL_BODY = prove
 (`!res buf table (inlist:byte list) pc (p:num) (L:num) stackpointer.
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table, 2048) /\
        p < 272 /\ L < 256 /\
        L = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) /\
        ~(L = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word L /\ read RCX s = word p /\
                  read(memory :> bytes(res, 4 * L)) s =
                    num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)))
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  (let outlist = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) in
                   read RAX s = word(LENGTH outlist) /\ read RCX s = word(p+1) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  SCALAR_BODY_SETUP THEN
  ASM_CASES_TAC `val(EL p (inlist:byte list)) MOD 16 < 9` THENL
   [(* ===== ACCEPT-LOW (low<9): step to pc+364, store low, to pc+379 ===== *)
    SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--14) THEN DISCARD_OLDSTATE_TAC "s14" THEN
    SUBGOAL_THEN `outlen0 + 1 < 256` ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->let c=concl th in c=`outlen0<256`||c=`val(EL p (inlist:byte list)) MOD 16 < 9`||c=`~(outlen0=255/\val(EL p (inlist:byte list)) MOD 16 < 9)`))) THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> let c=concl th in
       if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s14:x86state`))c
       then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
    SUBGOAL_THEN `~(&(val(word_zx(word(outlen0+1):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(outlen0+1):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (15--18) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL]) THEN DISCARD_OLDSTATE_TAC "s18" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
     [(* ACCEPT-ACCEPT *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (19--22) THEN
      SUBGOAL_THEN `val(word(outlen0+1):int64) = outlen0+1` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0+1<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (23--25) THEN DISCARD_OLDSTATE_TAC "s25" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s25:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0+1<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 2` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_BOTH) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE `(outlen0+1)+1 = outlen0+2`] THEN
      CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32;
                   word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 2) = 4 * outlen0 + 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s25:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32;
             word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
           `4*outlen0`; `8`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          (* 8-byte = [lo;hi] *)
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(REWRITE_CONV[APPEND] `APPEND [a:int32] [b:int32]`)] THEN
          SUBGOAL_THEN `(8:num) = 4 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `word_add res (word(4*outlen0)):int64`; `s25:x86state`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
             `4`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
          (* bridge both stores to spec form *)
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s25:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s25:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c
             then ASSUME_TAC(REWRITE_RULE[MATCH_MP HI_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) DIV 16 < 9`)] th) else NO_TAC) THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s25:x86state` `word_add res (word(4 * outlen0)):int64`;
            SUBGOAL_THEN `word_add (word_add res (word (4 * outlen0))) (word 4):int64 = word_add res (word (4 * (outlen0+1)))` SUBST1_TAC THENL
             [CONV_TAC WORD_RULE; ALL_TAC] THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s25:x86state` `word_add res (word(4 * (outlen0+1))):int64`]]];
      (* ===== LO-only (low<9, high>=9): jae pc+383 taken -> pc+314 ===== *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 9)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (19--20) THEN DISCARD_OLDSTATE_TAC "s20" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_LO) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s20:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
           `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s20:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          STORE4_FROM_SPEC `s20:x86state` `word_add res (word(4 * outlen0)):int64`]]];
    (* ===== REJECT-LOW (low>=9): jae pc+347 taken -> pc+371 ===== *)
    SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
       [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) MOD 16 < 9)`) THEN ARITH_TAC;
        MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] MOD_LT_EQ) THEN ARITH_TAC]; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL]) THEN DISCARD_OLDSTATE_TAC "s12" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
     [(* HI-only (low>=9, high<9): jae pc+383 not taken -> store at res+4*outlen0 -> pc+314 *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (13--16) THEN
      SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (17--19) THEN DISCARD_OLDSTATE_TAC "s19" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s19:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_HI) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_HI) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s19:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
           `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s19:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP HI_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) DIV 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          STORE4_FROM_SPEC `s19:x86state` `word_add res (word(4 * outlen0)):int64`]];
      (* NONE (low>=9, high>=9): jae pc+383 taken -> pc+314, no store *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 9)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (13--14) THEN DISCARD_OLDSTATE_TAC "s14" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_NONE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list = REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist)` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_NONE) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN RCX_INC_TAC]]);;

(* ========================================================================= *)
(* WOP WRAPPER -> MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL (replaces the CHEAT).     *)
(* SCALAR_TAIL_BODY (above) is the per-byte trip. The wrapper:                 *)
(*  Entry (pc+314): RAX=word outlen0, RCX=word(16N), outlen0=niblen(SUB(0,16N)) *)
(*    <= 280, res holds REJ(SUB(0,16N)).                                       *)
(*  Capped-output exit lemmas ALREADY PROVEN:                                  *)
(*    - count-exit: SUB_LIST_256_FROM_PARTIAL_REJ  (outlen=256 at pos k =>      *)
(*        SUB_LIST(0,256)(REJ inlist) = REJ(SUB(0,k))).                         *)
(*    - offset-exit: SUB_LIST_BYTE_272 (SUB(0,272)=inlist) + SUB_LIST_256_LE    *)
(*        (outlen<=256 => cap is identity) + REJ(SUB(0,272))=REJ inlist.        *)
(*  PLAN:                                                                      *)
(*   Phase A: entry case-split `outlen0 >= 256`.                               *)
(*     - outlen0>=256: by NIBLEN monotonicity outlen0<=280; but actually the    *)
(*       WOP precond forces outlen0=256 here is NOT guaranteed -- the SIMD loop  *)
(*       could leave outlen0 up to 280. HOWEVER cmp eax,256 jae fires           *)
(*       immediately (RAX>=256). Need outlen0=256 exactly for the postcond cap. *)
(*       Claim: at scalar-tail ENTRY outlen0 = min... NO. Re-examine: the SIMD  *)
(*       loop exited because (256<16N) or (248<niblen(16N)). If 248<niblen<=280  *)
(*       then outlen0 in (248,280]; the FIRST cmp eax,256 jae fires iff          *)
(*       outlen0>=256. If 248<outlen0<256 the byte loop runs a few more bytes.   *)
(*       The cap SUB_LIST(0,256) means: if final outlen reaches 256 -> 256 elts; *)
(*       else (input exhausted, pos=272) outlen<256 -> all of REJ inlist.        *)
(*     So entry case-split is really just the first guard; unify via the loop.  *)
(*   Phase B: ENSURES_WHILE over K = (#bytes consumed in tail) where K = M-16N,  *)
(*     M = smallest pos>=16N with outlen(M)>=256 \/ pos>=272. Body = SCALAR_TAIL_BODY *)
(*     specialized at p=16N+i (each clean trip: outlen(16N+i)<256, and           *)
(*     ~(outlen=255/\low<9) must hold for the body's no-mid-exit precond --       *)
(*     for i<K-1 trips outlen stays <255-ish; the LAST trip may mid-exit -> it's  *)
(*     the terminal segment, NOT a body trip).                                   *)
(*   Phase C: terminal trip (count/offset/mid-byte exit) -> pc+402, apply the    *)
(*     capped-output lemma matching the exit mode.                               *)
(*  GOTCHA: the body lemma's `~(L=255/\low<9)` precond is exactly what makes a    *)
(*  clean trip NOT mid-exit; the mid-byte exit (L=255, low<9 -> outlen hits 256  *)
(*  after the low store) is a SEPARATE terminal case landing at pc+402 with       *)
(*  outlen=256 (count-exit via SUB_LIST_256_FROM_PARTIAL_REJ at pos=16N+K, but    *)
(*  with the low nibble stored -- a half-byte; handle by stepping pc+314..pc+369  *)
(*  directly in the terminal segment).                                           *)
(*  Foundational arith: NIBLEN_BOUND_FROM_WOP (niblen(16N)<=280),               *)
(*  LENGTH_OUTLIST0_LE_280, SCALAR_TAIL_N_EQ_17 (offset case N=17).             *)
(* ========================================================================= *)
