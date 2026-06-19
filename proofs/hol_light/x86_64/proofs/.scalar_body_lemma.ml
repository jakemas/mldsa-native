(* ========================================================================= *)
(* SCALAR_TAIL per-byte body lemma — full cheat-free proof.                    *)
(* One trip pc+318 -> pc+318 consuming input byte at position p, extending     *)
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

(* Bridge a single nibble store `read(bytes32 a) s = word_sx(...)` (already in spec form)
   to `read(bytes(a,4)) s = val(word_sx(...))`. State name and address supplied via the goal. *)
let STORE_BYTES4_TAC sN =
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN REWRITE_TAC[VAL_WORD] THEN
  W(fun (_,g) ->
     (* find the bytes(...,4) read whose MOD we must drop *)
     let t = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="read" &&
         can (find_term (fun v -> try fst(dest_const(fst(strip_comb v)))="bytes" with _->false)) u
         with _->false) g in
     ignore t; ALL_TAC) THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;;

let SCALAR_TAIL_BODY = prove
 (`!res buf table (inlist:byte list) pc (p:num) (L:num) stackpointer.
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        p < 272 /\ L < 256 /\
        L = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) /\
        ~(L = 255 /\ val(EL p inlist) MOD 16 < 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 318) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word L /\ read RCX s = word p /\
                  read(memory :> bytes(res, 4 * L)) s =
                    num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)))
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 318) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  (let outlist = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) in
                   read RAX s = word(LENGTH outlist) /\ read RCX s = word(p+1) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  CHEAT_TAC);;
