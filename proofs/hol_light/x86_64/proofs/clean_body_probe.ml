(* Probe script: develop the CLEAN_BODY prologue + SIMD setup interactively as a
   standalone tactic block, checking that f0sub/mask8 reach chunk0-keyed spec
   form so SUBITER1_VALUE plugs in. NOT loaded by the main proof. *)

let PURGE_STALE_STATES_TAC names =
  let rec refs_stale tm = match tm with
    | Comb(Comb(Const("read",_),_),Var(nm,_)) when List.mem nm names -> true
    | Comb(a,b) -> refs_stale a || refs_stale b
    | Abs(_,b) -> refs_stale b
    | _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th -> if refs_stale (concl th) then ALL_TAC else failwith "keep"));;

let EXEC = MLDSA_REJ_UNIFORM_ETA4_EXEC;;

(* ---- R10/MOVZX capture helper (2026-06-11). The movzbl r8b->r10d at step 13
   is stepped with X86_VERBOSE_STEP_TAC (single state arg, keeps old-state reads,
   unlike X86_STEPS_TAC which discards them). Verbose leaves R10 as
   word_zx(word_zx(read (OPERAND8 (% r8b) (write RIP .. s12)) (write RIP .. s12)));
   OP8_R8B_READ + COMPONENT_READ_OVER_WRITE_CONV reduce it to
   word_zx(word_zx(word(val(read R8 s12) MOD 256))). ---- *)
let OP8_R8B_READ = prove
 (`!s:x86state. read (OPERAND8 (% r8b) s) s = word(val(read R8 s) MOD 256)`,
  GEN_TAC THEN REWRITE_TAC[OPERAND8; r8b; GPR8; register_size; regsize] THEN
  REWRITE_TAC[GSYM(NUM_EXP_CONV `2 EXP 8`)] THEN
  ONCE_REWRITE_TAC[MESON[EXP; DIV_1] `x MOD 2 EXP n = x DIV 2 EXP 0 MOD 2 EXP n`] THEN
  REWRITE_TAC[GSYM word_subword; READ_COMPONENT_COMPOSE; R8] THEN
  REWRITE_TAC[bottom_32; bottom_16; bottom_8; bottomhalf; READ_SUBWORD] THEN
  ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN REWRITE_TAC[BIT_WORD_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let MOVZBL_R10_CAPTURE_TAC : tactic =
  RULE_ASSUM_TAC(CONV_RULE(
    REWRITE_CONV[OP8_R8B_READ] THENC
    ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV));;

(* Drop any assumption whose RHS (or the whole eq) contains a raw word_join on
   chunk0 byte-subwords -- used to delete the raw vpmovzxbw form once the
   usimd16 form has been established, preventing re-explosion. *)
let DROP_WORDJOIN_TAC : tactic =
  fun (asl,w) ->
    (REPEAT(FIRST_X_ASSUM(fun th ->
       if can (find_term (fun u -> match u with Const("word_join",_) -> true | _ -> false))
              (concl th)
       then ALL_TAC else failwith "keep"))) (asl,w);;

let clean_body_tm = `
   !res buf table (inlist:byte list) pc N (i:num) stackpointer.
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        ~(N = 0) /\ i + 1 < N /\ 16 * (i+1) <= 256 /\
        LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i+1)) inlist)) <= 248
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 56) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                  read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
                  read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
                  read RCX s = word(16*i) /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s = num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist)))
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 56) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                  read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
                  read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list)) /\
                  read RCX s = word(16*(i+1)) /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list))) s = num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist)))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`;;

g clean_body_tm;;

(* ---- prologue: setup + guards -> pc+79 / s4 ---- *)
e(REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  (* Fold LENGTH(REJ_SAMPLE..(0,16i))->outlen0 in the RAX/memory assumptions, but KEEP the
     outlen0 definition itself (the mid-guard needs it to fold SUBITER_OUTLEN_BOUND_1 and the
     final postcondition needs to reconstruct LENGTH(REJ_SAMPLE..(0,16(i+1)))).  Grab the def
     as a named theorem first, RULE_ASSUM with it, then re-ASSUME it. *)
  FIRST_ASSUM(fun th -> if concl th =
      `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) else NO_TAC) THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  VAL_INT64_TAC `outlen0:num`);;

e(X86_STEPS_TAC EXEC (1--2));;
e(SUBGOAL_THEN `read RIP s2 = word(pc + 67):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 318`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC]);;
e(X86_STEPS_TAC EXEC (3--4));;
e(SUBGOAL_THEN `read RIP s4 = word(pc + 79):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&256:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 318`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC]);;

(* ---- vpmovzxbw + fold YMM0 to usimd16 word_zx chunk0 ---- *)
e(X86_VSTEPS_TAC EXEC (5--5));;
e(SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `16*i <= 256` THEN ARITH_TAC; ALL_TAC]);;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(16*i):int64) = 16*i`; ARITH_RULE `1 * x = x`]));;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read (memory :> bytes128 (word_add buf (word (16 * i)))) s4 = chunk0`]));;
e(SUBGOAL_THEN `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s5`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC]);;
(* probe checkpoint: at this point read YMM0 s5 = usimd16 word_zx chunk0. *)

(* Discard the raw word_join YMM0 s5 eq, keep usimd; purge stale s4. *)
e(DROP_WORDJOIN_TAC);;
e(PURGE_STALE_STATES_TAC ["s4"]);;

(* Steps 6,7,8 vpsllw/vpor/vpand: thread the usimd YMM0 form forward, then at
   s8 establish read YMM0 s8 = the EXACT chunk0-keyed f0nib chain via WORD_BLAST. *)
e(X86_VSTEPS_TAC EXEC (6--6));;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256`]));;
e(X86_VSTEPS_TAC EXEC (7--7));;
e(X86_VSTEPS_TAC EXEC (8--8));;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM2 s5 =
    word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256`]));;

(* abbreviation for the f0nib chunk0 chain *)
let F0NIB_CHUNK0 =
  `word_and (word_or (usimd16 (\b:byte. word_zx b:int16) chunk0:int256)
                     (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) chunk0:int256):int256))
            (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)`;;

e(SUBGOAL_THEN (mk_eq(`read YMM0 s8:int256`, F0NIB_CHUNK0)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s8`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC]);;
e(DROP_WORDJOIN_TAC);;
e(PURGE_STALE_STATES_TAC ["s5";"s6";"s7"]);;

(* CRITICAL LAYERING: abbreviate f0nib = fn OPAQUE, keep the 16 byte-facts
   (word_subword fn (8j,8) = word(nibble_j)) from F0NIB_BYTES(chunk0). This keeps
   f0sub/f1bnd SMALL (word_join over the variable fn, ~2.3k chars) so per-byte
   lane extraction is fast. *)
e(ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES));;
e(ABBREV_TAC `fn:int256 = read YMM0 s8`);;
e(RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME(mk_eq(`fn:int256`, F0NIB_CHUNK0)))]));;
(* now assumptions carry: read YMM0 s8 = fn, and the 16 facts word_subword fn (8j,8)=word(nibble) *)

(* Step 9 vpsubb ymm1 <- ymm0(fn) - ymm4(bound). YMM1 s9 = word_join over fn (small). *)
e(X86_VSTEPS_TAC EXEC (9--9));;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s8 = fn:int256`;
   ASSUME `read YMM4 s8 = word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256`]));;
e(ABBREV_TAC `f1bnd:int256 = read YMM1 s9`);;

(* Step 10 vpsubb ymm0 <- ymm3(eta) - ymm0(fn). YMM0 s10 = word_join over fn (small). *)
e(X86_VSTEPS_TAC EXEC (10--10));;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s9 = fn:int256`;
   ASSUME `read YMM3 s9 = word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256`]));;

(* abbreviate f0sub (keeps f0sub = <word_join over fn> in assumptions). *)
e(ABBREV_TAC `f0sub:int256 = read YMM0 s10`);;

(* ---- gather-byte SUBGOAL: the SUBITER_STORE_SPEC gather hyp, g = word_subword f0sub (0,128).
   Per lane: case-split j, NUM_REDUCE, MERGE the double-subword (0,128)+(8j,8) via
   WORD_SUBWORD_SUBWORD, rewrite f0sub's word_join def, JOIN-extract (NOT WORD_BLAST),
   then close with the fn byte-facts (word_subword fn (k,8)=word(nibble)). ---- *)
e(SUBGOAL_THEN
   `!j. j < 8 ==>
      word_subword (word_subword (f0sub:int256) (0,128):int128) (8*j,8):byte =
      word_sub (word 4) (word_subword (fn:int256) (8*j,8):byte)`
   ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let f0sub_wj_eq = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let fnf = find (fun th -> is_conj(concl th) && can(find_term(fun u->u=`fn:int256`)) (concl th)
                               && can(find_term(fun u->u=`chunk0:int128`)) (concl th)) (map snd asl) in
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
        (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
      REWRITE_TAC[f0sub_wj_eq] THEN
      REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
               DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
        CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN REWRITE_TAC[fnf]);
    ALL_TAC]);;

(* ---- mask-bit SUBGOAL: bit 7 of f1bnd lane k <=> nibble_k < 9 (k<8) ----
   the SUBITER_STORE_SPEC mask predicate, per lane via JOIN extract + VPSUBB_SIGN_BIT_LT_9.
   f1bnd_wj/fn_byte_facts located INSIDE the tactic (via the live goal's own asms) to
   avoid top_goal()-timing issues across the multi-goal gather SUBGOAL. *)
e(SUBGOAL_THEN
   `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*k,8):byte) <=>
                   val(word_subword (fn:int256) (8*k,8):byte) < 9)`
   ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let f1bnd_wj_eq = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let fnf = find (fun th -> is_conj(concl th) && can(find_term(fun u->u=`fn:int256`)) (concl th)
                               && can(find_term(fun u->u=`chunk0:int128`)) (concl th)) (map snd asl) in
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
        (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[f1bnd_wj_eq] THEN
      REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
               DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
        CONV_TAC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[WORD_SUBWORD_BYTE_ID; fnf] THEN
      MATCH_MP_TAC VPSUBB_SIGN_BIT_LT_9 THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
      W(fun (asl2,w2) ->
         let bytetm = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
           type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
         MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bytetm VAL_BOUND))) THEN ARITH_TAC);
    ALL_TAC]);;
e(PURGE_STALE_STATES_TAC ["s8";"s9"]);;

(* ---- drop the huge f0sub/f1bnd word_join defs BEFORE vpmovmskb; gather+maskbit forall facts
   suffice now. This keeps mask8 (vpmovmskb of f1bnd) and all downstream terms small
   (f0sub/f1bnd stay opaque vars). ---- *)
e(REPEAT(FIRST_X_ASSUM(fun th ->
   if (is_eq(concl th) && (lhand(concl th) = `f0sub:int256` || lhand(concl th) = `f1bnd:int256`))
   then ALL_TAC else failwith "keep")));;

(* Step 11 vpmovmskb r8d <- ymm1(f1bnd opaque): R8 s11 = word_zx(word(bitval-sum over
   bit 7 (word_subword f1bnd (8k,8)))) — moderate (f1bnd opaque).  Do NOT opaque-REABBREV R8:
   keep its explicit bitval-sum value so the downstream movzbl R10 is a state-free term that
   survives DISCARD (per CLEAN_BODY_dev lesson: opaque REABBREV + PURGE breaks the popcnt chain). *)
e(X86_VSTEPS_TAC EXEC (11--11));;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM1 s10 = f1bnd:int256`]));;
e(PURGE_STALE_STATES_TAC ["s10"]);;

(* Step 12: vextracti128 $0 f0sub -> xmm5.  Establish read YMM5 s12 = word_subword f0sub (0,128)
   (= SUBITER_STORE_SPEC's g) explicitly so the gather hyp transfers; then REABBREV g0a keeping
   the eq g0a = word_subword f0sub (0,128). *)
e(X86_VSTEPS_TAC EXEC (12--12));;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s11 = f0sub:int256`]));;
e(SUBGOAL_THEN `read YMM5 s12 = word_subword (f0sub:int256) (0,128):int128` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM5 s12`))(lhand(concl th))
                            then SUBST1_TAC th else NO_TAC) THEN
    CONV_TAC WORD_BLAST;
    ALL_TAC]);;
e(PURGE_STALE_STATES_TAC ["s11"]);;
(* probe checkpoint 3: at s12, read YMM5 s12 = word_subword f0sub (0,128) (= g for the store),
   f0sub/f1bnd opaque, gather+maskbit forall facts retained, mask8 abbreviated.
   The gather hyp `word_subword (word_subword f0sub (0,128))(8j,8)=word_sub 4(word_subword fn(8j,8))`
   is exactly word_subword (read YMM5 s12) (8j,8) = ..., ready for SUBITER_STORE_SPEC. *)

(* ---- SUB-ITER 1 store + counters — VALIDATED 2026-06-11 with R10 capture ---- *)

(* Step 13: movzbl r8b->r10d.  CRITICAL: step with X86_VERBOSE_STEP_TAC (keeps the
   old-state read, unlike X86_STEPS which discards it), then MOVZBL_R10_CAPTURE_TAC
   reduces OPERAND8(%r8b) to word(val(read R8 s12) MOD 256).  Then REABBREV r10v so
   the popcnt result at s18 references the stable VAR r10v (survives DISCARD_OLDSTATE). *)
(* Abbreviate read R8 s12 as mask8 FIRST so the movzbl result references the stable
   VAR mask8 (not the discarded state s12) and survives DISCARD_OLDSTATE downstream. *)
e(REABBREV_TAC `mask8 = read R8 s12`);;
e(X86_VERBOSE_STEP_TAC EXEC "s13");;
e(MOVZBL_R10_CAPTURE_TAC);;
(* The capture re-introduces `read R8 s12` (via COMPONENT_READ_OVER_WRITE_CONV); fold it back
   to the stable var mask8 so read R10 s13 = word_zx(word_zx(word(val mask8 MOD 256))) is
   keyed ONLY on mask8 — it then survives DISCARD_OLDSTATE through the store, and the popcnt
   result at s18 (popcount over R10) reduces to popcount of mask8's low byte. *)
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s12 = mask8`]));;

(* Steps 14-17: vmovq table[r10]->xmm6 ; vpshufb ; vpmovsxbd ; vmovdqu STORE. *)
e(X86_VSTEPS_TAC EXEC (14--14));;
e(REABBREV_TAC `tab1 = read YMM6 s14`);;
e(X86_VSTEPS_TAC EXEC (15--15));;
e(REABBREV_TAC `pshuf1 = read YMM6 s15`);;
e(PURGE_STALE_STATES_TAC ["s14"]);;
e(X86_VSTEPS_TAC EXEC (16--16));;
e(REABBREV_TAC `sx1 = read YMM1 s16`);;
e(PURGE_STALE_STATES_TAC ["s15"]);;
e(X86_STEPS_TAC EXEC (17--17));;         (* STORE at memory:>bytes256(res + 4*outlen0) *)
e(PURGE_STALE_STATES_TAC ["s16"]);;
(* probe checkpoint 7: at s17/pc+141. sub-iter 1 stored sx1 (the int32 block) at res+4*outlen0;
   read R10 s13 = r10v stable; the prefix bytes(res,4*outlen0) untouched. *)

(* Steps 18-21: popcnt r10d->r9d ; add eax,r9d ; shr r8d,8 ; add ecx,4.
   With r10v stable, R9 s18 = word(popcount(word_zx r10v)) and RAX s19 = outlen0+that
   survive (no discarded-state reference). *)
e(X86_STEPS_TAC EXEC (18--21));;
e(PURGE_STALE_STATES_TAC ["s17";"s18";"s19";"s20"]);;
(* probe checkpoint 8: at s21/pc+156, sub-iter 1 complete incl. counters. NEXT:
   - prove RAX s21 = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16i+4) inlist))) via
     RAX_BOUND_AFTER_POPCNT_ADD_DIRECT + POPCNT_NIBBLES_4_BYTES_BRIDGE (popcount(r10v low) =
     |accepted nibbles in block 0| = len of REJ_SAMPLE block), and the store value via
     SUBITER_STORE_SPEC composed with SUBITER_OUTLEN_STEP_4 / REJ_SAMPLE_ETA4_BYTES_STEP_16;
   - mid-guard cmp eax,248 / ja (pc+156): JA_NOT_TAKEN_LE (RAX<=248 on clean iter via
     niblen(16i+4)<=niblen(16(i+1))<=248 + CLEAN_BLOCK_BOUNDS) -> fall through;
   - sub-iters 2,3,4 (vpsrldq $8 / vextracti128 $1 for g; mask already >>8; HI lemmas for 3,4);
   - after sub-iter 4: RCX=16(i+1), RAX=niblen(16(i+1)); jmp pc+56; ENSURES_FINAL_STATE_TAC. *)

(* ======================= SUB-ITER 1 MID-GUARD (VALIDATED 2026-06-11) ======================= *)
(* The `cmp eax,248; ja` at pc+156 must FALL THROUGH (no exit to scalar tail). Chain:
   R9/RAX popcount(vpmovmskb low byte) -> 8-bitval sum -> = block accept count
   -> outlen0+count <= 248 -> RAX = word(outlen0+count) -> JA_NOT_TAKEN_LE -> RIP=pc+161. *)

(* (1) bring the 4 block-byte facts: SUB_LIST(16i+4k,4) inlist = [chunk0 slice]. *)
e(MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH(inlist:byte list) = 272` THEN
    UNDISCH_TAC `16 * i <= 256` THEN ARITH_TAC;
    STRIP_TAC]);;

(* (2) expand mask8 -> its bitval-sum def in RAX/R9, then reduce the popcount of the
   vpmovmskb low byte to the 8-bitval sum (POPCNT_VPMOVMSKB low-byte reduction, inlined
   on the exact stepped popcount term so the word_zx widths match). *)
e(W(fun (asl,w) ->
   let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM m8def])));;
e(W(fun (asl,w) ->
   let r9 = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s21",_))),_) -> true | _ -> false) asl in
   let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
   let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
            bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
            bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
            bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
   let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
              (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
   SUBGOAL_THEN (mk_eq(goal_pc, low8)) ASSUME_TAC THENL
    [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
     REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
     CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
     MAP_EVERY (fun b -> BOOL_CASES_TAC b)
       [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
        `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
        `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
        `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
     REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (mk_eq(goal_pc, low8))])));;

(* (3) 8-bitval sum = LENGTH(REJ_NIBBLES_ETA4 block0) via maskbit forall + fn-facts + bridges. *)
e(W(fun (asl,w) ->
   let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c) asl) in
   let mbits = map (fun k -> let th=SPEC(mk_small_numeral k) maskbit in
        CONV_RULE NUM_REDUCE_CONV (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
   let fnf = find (fun (_,th) -> is_conj(concl th) && can(find_term(fun u->u=`fn:int256`))(concl th)
                  && can(find_term(fun u->u=`chunk0:int128`))(concl th)) asl in
   let blk0 = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
          (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
   let bitsum8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
            bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
            bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
            bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
   SUBGOAL_THEN (mk_eq(bitsum8, `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)`)) ASSUME_TAC THENL
    [REWRITE_TAC mbits THEN REWRITE_TAC[snd fnf; snd blk0] THEN
     REWRITE_TAC[BITVAL_SUM_8_EQ_LENGTH_FILTER; LENGTH_FILTER_BYTE_NIBBLES_4_BYTES];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (mk_eq(bitsum8, `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)`))])));;

(* (4) outlen0 + block <= 248 (SUBITER_OUTLEN_BOUND_1, folding LENGTH(REJ_SAMPLE..(0,16i))->outlen0). *)
e(SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i,4) inlist):int16 list) <= 248` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_1) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `LENGTH(inlist:byte list) = 272` THEN UNDISCH_TAC `16*(i+1)<=256` THEN ARITH_TAC;
        ASM_REWRITE_TAC[]];
      W(fun (asl,_) -> let o0 = find (fun (_,th) -> match concl th with
         Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asl in
       REWRITE_TAC[snd o0])];
    ALL_TAC]);;

(* (5) RAX = word(outlen0 + block) via RAX_NEST_REDUCE. *)
e(W(fun (asl,w) ->
   let bnd = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_) -> true | _ -> false) asl in
   let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) (snd bnd) in
   RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RAX_NEST_REDUCE lt32])));;

(* (6) step the cmp eax,248 (s22): JA_NOT_TAKEN_LE -> RIP s22 = pc+161 (falls through). *)
e(VAL_INT64_TAC `outlen0 + LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i,4) inlist):int16 list)`);;
e(MP_TAC(SPECL [`outlen0 + LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i,4) inlist):int16 list)`;`248`] JA_NOT_TAKEN_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC);;
e(X86_STEPS_TAC EXEC (22--22));;
(* probe checkpoint 10: RIP s22 = word(pc+161). Sub-iter 1 mid-guard DISCHARGED. RAX = word(outlen0+block0).
   NEXT (store value + sub-iters 2-4): see reference_x86_body_restructure "STORE-VALUE" + the
   sub-iter 2-4 plan. *)



(* ============================================================================
   STORE-VALUE BRIDGE LEMMAS (2026-06-11) — proven this session, reusable for
   all 4 sub-iters. pshuf1:int256 (vpshufb on full YMM). Store reads low 64 bits
   = low 128-lane = PSHUFB_OUT_BYTE form (j<8). DO NOT retype pshuf1 as int128.
   ============================================================================ *)

(* PSHUF1_STRUCT_USIMD: the stepped pshuf1 structural value (word_zx(word_join 16))
   equals word_zx(usimd16 F (word_zx tab1)), F the standard PSHUFB gather body.
   This is PROVED generically by flattening usimd16 -> nested word_subword and
   collapsing via WORD_SUBWORD_SUBWORD. The exact statement is built per-context
   from the stepped def (the word_join nest); proof tactic that closes it:
     REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV)
     THEN SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;
                   DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH]
     THEN CONV_TAC NUM_REDUCE_CONV
   (validated: closes in ~0.8s on the live sub-iter-1 pshuf1). *)

(* IDX_RED: table index reduction. mask8:int64 (the vpmovmskb result). *)
let IDX_RED_ETA4 = prove
 (`val (word_zx (word_zx (word (val (mask8:int64) MOD 256):byte):int32):int64) =
   val mask8 MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD] THEN
  SIMP_TAC[DIMINDEX_64;DIMINDEX_32;DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val (mask8:int64) MOD 256 < 256` ASSUME_TAC THENL
   [ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT;
      ARITH_RULE `n < 256 ==> n < 256 /\ n < 4294967296 /\ n < 18446744073709551616`]]);;

(* IN-CONTEXT (NOT standalone — carries the live goal's 12 state-transition hyps):
   tab1_eq:  tab1 = word_zx(word_zx(word(num_of_wordlist(TABLE_ENTRY(word(val mask8 MOD 256))))))
     via:  TABLE_VMOVQ_READ (table, val mask8 MOD 256, s13) discharged by the
           table-read s13 assumption + (val mask8 MOD 256 < 256);
           REWRITE_RULE[IDX_RED_ETA4] on the tab1 def to align the index;
           GSYM(REWRITE_RULE[raw_eq] tabdef').
   wzt_eq:  word_zx tab1 :int128 = word_zx(word_zx(word(num...):int64):int128):int128
            (the PSHUFB_OUT_BYTE control form) via REWRITE[tab1_eq] THEN
            GSYM VAL_EQ THEN VAL_WORD_ZX_GEN/VAL_WORD THEN DIMINDEX THEN
            MOD_MOD_EXP_MIN (keep moduli as 2 EXP n, do NOT NUM_REDUCE first) THEN reduce.
            MUST be done in-context (tab1_eq has hyps), as a SUBGOAL_THEN.
   Then: PSHUF1_STRUCT_USIMD + wzt_eq put pshuf1 in PSHUFB_OUT_BYTE-ready form;
         PSHUFB_OUT_BYTE (j<8) gives pshuf1 byte j = word_subword g (8*val(EL j TABLE_ENTRY),8);
         VPMOVSXBD_LANE_EXTRACT on the stepped YMM1 word_join gives
           word_subword (read YMM1 sN) (32j,32) = word_sx(pshuf1 byte j);
         SUBITER1_VALUE + PSHUFB_OUT_LIST_AS_MAP give EL j (REJ_SAMPLE block) = word_sx(...);
         => lane-match hyp of STORE_BYTES256_NUM_OF_WORDLIST. *)

(* === PSHUF1_LOWLANE_BYTE (2026-06-11, PROVEN standalone, 0 hyps) ============
   The complete store-value byte bridge. Outer word_zx 256<-128 is transparent
   for low-lane bytes (j<8); reduces directly to PSHUFB_OUT_BYTE.
   NOTE: structural pshuf1 F uses (4)word index extraction; PSHUFB_OUT_BYTE uses
   (8)word — bridged by VAL4EQ8 (val of word_subword (0,4) is width-independent). *)

let WSZ_OK = prove
 (`!(x:int128) j. j < 8
    ==> word_subword (word_zx x:int256) (8 * j,8):byte = word_subword x (8 * j,8)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`x:int128`; `8*j`; `8`]
    (INST_TYPE [`:256`,`:N`; `:128`,`:M`; `:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_128;DIMINDEX_256] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let VAL4EQ8 = prove
 (`!i:byte. val(word_subword i (0,4):4 word) = val(word_subword i (0,4):8 word)`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD] THEN
  SIMP_TAC[DIMINDEX_4;DIMINDEX_8;DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let PSHUF1_LOWLANE_BYTE = prove
 (`!g m j. j < 8
    ==> word_subword
          (word_zx
            (usimd16 (\i. if bit 7 i then word 0:byte
                          else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
          (8 * j,8):byte
        = word_subword g (8 * val (EL j (TABLE_ENTRY m)),8)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WSZ_OK] THEN
  REWRITE_TAC[VAL4EQ8] THEN ASM_SIMP_TAC[PSHUFB_OUT_BYTE]);;

(* === FULL VALUE-CHAIN CAPSTONE (2026-06-11, all PROVEN standalone, 0 hyps) ===
   STORE_LANE_MATCH is the complete sub-iter store lane bridge: lane j of the
   YMM store value (vpshufb->vpmovsxbd pipeline in PSHUFB structural form) equals
   word_sx(EL j (PSHUFB_OUT_LIST g m)). Feeds STORE_BYTES256_NUM_OF_WORDLIST's
   lane-match hyp once combined with SUBITER1_VALUE (EL j REJ block = word_sx(...)). *)

let LENGTH_TABLE_ENTRY = prove
 (`!m:byte. LENGTH(TABLE_ENTRY m) = 8`,
  GEN_TAC THEN REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST; LENGTH_MLDSA_REJ_UNIFORM_TABLE] THEN
  MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let PSHUF1_BYTE_EQ_OUTLIST = prove
 (`!g m j. j < 8
    ==> word_subword
          (word_zx
            (usimd16 (\i. if bit 7 i then word 0:byte
                          else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
          (8 * j,8):byte
        = EL j (PSHUFB_OUT_LIST g m)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PSHUF1_LOWLANE_BYTE] THEN
  ASM_SIMP_TAC[PSHUFB_OUT_LIST_AS_MAP; EL_MAP; LENGTH_TABLE_ENTRY]);;

let VPMOVSXBD_LANE_J = prove
 (`!(x:int64) j. j < 8
    ==> word_subword (usimd8 (\b:byte. word_sx b:int32) x) (32*j,32):int32
        = word_sx (word_subword x (8*j,8):byte)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `j < 8 <=> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VPMOVSXBD_LANE_EXTRACT]);;

let WZZ_LOW = prove
 (`!(p:int256) j. j < 8
    ==> word_subword (word_zx (word_zx p:int128):int64) (8*j,8):byte = word_subword p (8*j,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_zx (p:int256):int128`;`8*j`;`8`]
    (INST_TYPE[`:64`,`:N`;`:128`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  MP_TAC(ISPECL [`p:int256`;`8*j`;`8`]
    (INST_TYPE[`:128`,`:N`;`:256`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
  SUBGOAL_THEN `MIN (8*j+8) 128 <= 256 /\ MIN (8*j+8) 256 <= 128 /\ MIN(8*j+8) 128 <= 64` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> REWRITE_TAC[th2;th1]))]);;

let STORE_LANE_MATCH = prove
 (`!(g:int128) m j. j < 8
    ==> word_subword
          (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx
              (word_zx
                (usimd16 (\i. if bit 7 i then word 0:byte
                              else word_subword g (8 * val (word_subword i (0,4):4 word),8))
                  (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
              :int128):int64))
          (32*j,32):int32
        = word_sx (EL j (PSHUFB_OUT_LIST g m))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VPMOVSXBD_LANE_J] THEN ASM_SIMP_TAC[WZZ_LOW] THEN
  ASM_SIMP_TAC[PSHUF1_BYTE_EQ_OUTLIST]);;

(* === SUBITER->LANE CONNECTOR (2026-06-12, PROVEN, 0 hyps) ==================
   STORE_LANE_EQ_REJBLOCK: ties STORE_LANE_MATCH to the exact SUB_LIST/MAP shape
   of SUBITER1_VALUE's RHS, so YMM lane j (j<k<=8) = EL j (MAP word_sx
   (SUB_LIST(0,k)(PSHUFB_OUT_LIST g m))) = EL j REJ_block (by SUBITER1_VALUE).
   This is precisely STORE_BYTES256_NUM_OF_WORDLIST's lane-match hyp. *)

let LENGTH_PSHUFB_OUT_LIST = prove
 (`!g:int128. !m:byte. LENGTH(PSHUFB_OUT_LIST g m) = 8`,
  REWRITE_TAC[PSHUFB_OUT_LIST_AS_MAP; LENGTH_MAP; LENGTH_TABLE_ENTRY]);;

let STORE_LANE_EQ_REJBLOCK = prove
 (`!(g:int128) m k j. j < k /\ k <= 8
    ==> word_subword
          (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
                else word_subword g (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64))
          (32*j,32):int32
        = EL j (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j < 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[STORE_LANE_MATCH] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,k)(PSHUFB_OUT_LIST (g:int128) m)) = k` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_MAP] THEN
    ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_PSHUFB_OUT_LIST; ADD_CLAUSES] THEN ASM_ARITH_TAC]);;

(* === SINGLE-STORE FULL BRIDGE + MEMORY COMPOSE (2026-06-12, PROVEN) ========
   SUBITER_STORE_POSTCOND: bytes256 store value (PSHUFB pipeline form), k<=8
     => read(bytes(A,4k)) = num_of_wordlist(MAP word_sx (SUB_LIST(0,k)(PSHUFB_OUT_LIST g m))).
     Lane-match discharged internally via STORE_LANE_EQ_REJBLOCK.
   SUBITER_STORE_EXTEND: fold a fresh int32 block at res+4|prefix| into the prefix
     => read(bytes(res, 4|prefix|+4|block|)) = num_of_wordlist(APPEND prefix block).
   Together with SUBITER1_VALUE (block = REJ_SAMPLE block) and REJ_SAMPLE_ETA4_BYTES_APPEND
   these give one sub-iter's extended-prefix memory postcondition end to end. *)

let SUBITER_STORE_POSTCOND = prove
 (`!A s (g:int128) m k.
     k <= 8 /\
     read (memory :> bytes256 A) s =
       (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
                else word_subword g (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64))
     ==> read (memory :> bytes(A, 4 * k)) s =
         num_of_wordlist (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:int64`;
    `usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
                else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64)`;
    `MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST (g:int128) m))`;
    `k:num`; `s:x86state`] STORE_BYTES256_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STORE_LANE_EQ_REJBLOCK THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let SUBITER_STORE_EXTEND = prove
 (`!res s (prefix:int32 list) (block:int32 list).
     read (memory :> bytes(res, 4 * LENGTH prefix)) s = num_of_wordlist prefix /\
     read (memory :> bytes(word_add res (word (4 * LENGTH prefix)), 4 * LENGTH block)) s
       = num_of_wordlist block
     ==> read (memory :> bytes(res, 4 * LENGTH prefix + 4 * LENGTH block)) s
         = num_of_wordlist (APPEND prefix block)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s:x86state`;
                 `prefix:int32 list`; `block:int32 list`;
                 `4 * LENGTH(prefix:int32 list)`; `4 * LENGTH(block:int32 list)`]
        (INST_TYPE [`:32`,`:N`] BYTES_EQ_NUM_OF_WORDLIST_APPEND)) THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]);;

(* === CLEAN_BODY ASSEMBLY PLAN (2026-06-12) ================================
   The generic store machinery is COMPLETE and committed in the main file:
     WSZ_OK, VAL4EQ8, PSHUF1_LOWLANE_BYTE, VPMOVSXBD_LANE_J, WZZ_LOW,
     LENGTH_TABLE_ENTRY, PSHUF1_BYTE_EQ_OUTLIST, STORE_LANE_MATCH,
     LENGTH_PSHUFB_OUT_LIST, STORE_LANE_EQ_REJBLOCK,
     SUBITER_STORE_POSTCOND, SUBITER_STORE_EXTEND.

   IN-CONTEXT per-sub-iter recipe at each vmovdqu store (NO new standalone
   lemma needed -- verified the composition mechanically):
     1. The stepped store value is a word_join nest; SUBGOAL_THEN it equals
        `usimd8 (\b. word_sx b) <word_zx(word_zx(word_zx(usimd16 F (word_zx(word_zx
         (word(num_of_wordlist(TABLE_ENTRY m)))))))) >` via the usimd8-unfold +
        WORD_BLAST recipe (same as the validated read YMM1 s16 = usimd8... step),
        AFTER rewriting pshuf to PSHUFB form [PSHUF1_STRUCT_USIMD + in-context
        tab1/wzt control bridge, which carry the goal's state hyps].
     2. MATCH_MP SUBITER_STORE_POSTCOND <that bytes256 store fact> -- unifies
        g:=G(q), m:=M(q), k automatically; needs k<=8 (LENGTH_REJ_SAMPLE_ETA4_BYTES_4).
     3. REWRITE[SUBITERn_VALUE] collapses num_of_wordlist(MAP word_sx(SUB_LIST...))
        -> num_of_wordlist(REJ_SAMPLE_ETA4_BYTES[4-byte chunk]).   [VERIFIED via REWRITE_CONV]
     4. SUBITER_STORE_EXTEND folds the block at res+4*outlen_so_far into the prefix.
   After 4 sub-iters: REJ_SAMPLE_ETA4_BYTES_16_AS_4 recombines the 4 four-byte
   blocks; REJ_SAMPLE_ETA4_BYTES_STEP_16 ties SUB_LIST(0,16i)++SUB_LIST(16i,16)
   = SUB_LIST(0,16(i+1)). Then jmp pc+56 + ENSURES_FINAL_STATE_TAC.

   CLEAN_BODY statement = BODY_CHEAT's (main file lines 4564-4606) restricted to
   the clean i+1<N case (RIP post = pc+56, RCX post = word(16*(i+1))). The probe
   here (clean_body_tm) is that exact spec; it reaches s22 (mid-guard discharged,
   RIP s22 = pc+161, RAX = word(outlen0+block0)). Continue stepping the 4
   sub-iter stores from s22 applying the recipe above. *)

(* === LIVE REPLAY NOTE (2026-06-12) ========================================
   Replayed prologue -> s12 fresh in the fully-loaded main-file session: works.
   ONE discrepancy vs the s11-12 block above: the vextracti128 $0 at step 12
   yields  read YMM5 s12 = word_zx (word_subword f0sub (0,128))  -- an EXTRA
   word_zx (128<-128, identity) wrapper. The probe's `SUBGOAL read YMM5 s12 =
   word_subword f0sub (0,128) ... CONV_TAC WORD_BLAST` does NOT reliably add the
   bare-subword assumption (WORD_BLAST proves it but the form isn't retained as
   wanted). FIX that worked live:
       let wzx_id = prove(`!x:int128. word_zx x:int128 = x`, REWRITE_TAC[WORD_ZX_TRIVIAL]);;
       e(RULE_ASSUM_TAC(REWRITE_RULE[wzx_id]));;
   This collapses YMM5 s12 to `word_subword f0sub (0,128)` (= g) directly, and
   also simplifies any other word_zx:128->128 noise. Do this right after step 12
   instead of the SUBGOAL_THEN. State after: s12, RIP=pc+116, g=word_subword
   f0sub (0,128), gather hyp (asm) `!j<8. word_subword (word_subword f0sub(0,128))
   (8j,8) = word_sub (word 4)(word_subword fn (8j,8))`, maskbit hyp present,
   f0sub/f1bnd opaque. Ready for the R10 capture (step 13) + sub-iter 1 store. *)

(* === LIVE STATE AT SUB-ITER 1 STORE (s17), 2026-06-12 =====================
   Replayed live in the fully-loaded session through step 17 (the vmovdqu store).
   The store fact (assumption):
     read (memory :> bytes256 (word_add res (word (4 * outlen0)))) s17 = sx1
   with the abbreviations:
     sx1   = word_join(... word_sx (word_subword (word_zx (word_zx pshuf1)) (8j,8)) ...)
             [the lane-extracted vpmovsxbd output -- matches USIMD8_SX_AS_JOIN /
              VPMOVSXBD_LANE_J pattern]
     pshuf1 = word_zx (word_join (if bit 7 (word_subword (word_zx tab1) (8j,8))
                then word 0
                else word_subword (word_zx (word_zx (word_subword f0sub (0,128))))
                       (8 * val (word_subword (word_zx tab1) (8j,4)),8)) ...)
             [the PSHUFB structural form: g = word_zx(word_zx(word_subword f0sub
              (0,128))), control = word_zx tab1]  -- matches PSHUF1_STRUCT_USIMD.
     tab1  = word_zx(word_zx(read(memory:>bytes64(word_add table
                (word(8*val(word_zx(word_zx(word(val mask8 MOD 256))))))))) s13))
             [the vmovq table gather -- matches TABLE_VMOVQ_READ after IDX_RED_ETA4].

   REMAINING value bridge (in-context, the only non-mechanical step left):
     A. sx1 = usimd8 (\b. word_sx b) (word_zx (word_zx pshuf1))
        via REWRITE[sx1 def] THEN usimd8-unfold + WORD_BLAST  (validated prior session).
     B. pshuf1 = word_zx (usimd16 F (word_zx tab1))   [PSHUF1_STRUCT_USIMD recipe:
        REWRITE[usimd16;usimd8;usimd4;usimd2] + DEPTH BETA + SIMP[WORD_SUBWORD_SUBWORD;
        DIMINDEX_*;ARITH] + NUM_REDUCE]  (proven prior session).
     C. word_zx tab1 = word_zx(word_zx(word(num_of_wordlist(TABLE_ENTRY
          (word(val mask8 MOD 256)))))):int128  [TABLE_VMOVQ_READ (table-read s13 +
        val mask8 MOD 256 < 256) + IDX_RED_ETA4 + GSYM; then GSYM VAL_EQ + VAL_WORD_ZX_GEN
        + MOD_MOD_EXP_MIN; carries the goal's state hyps so MUST be in-context].
     Substituting A,B,C makes the store value EXACTLY SUBITER_STORE_POSTCOND's
     argument with g := word_zx(word_zx(word_subword f0sub (0,128))),
     m := word(val mask8 MOD 256).  Then:
        MATCH_MP SUBITER_STORE_POSTCOND <store256 fact, k:=block len, k<=8>
        THEN REWRITE[SUBITER1_VALUE]  ==>  the 4*k stored bytes = num_of_wordlist
        (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (16*i,4) inlist)).
     Then SUBITER_STORE_EXTEND folds onto the res-prefix. (Repeat for sub-iters
     2,3,4 with their g from vpsrldq/vextracti128.)  *)

(* === LIVE VALUE-BRIDGE PROGRESS (2026-06-12) ==============================
   At the s17 store, Steps A and B of the value bridge were COMPLETED LIVE:
     A. sx1 = usimd8 (\b. word_sx b) (word_zx (word_zx pshuf1))
        TACTIC (works): SUBGOAL_THEN <that> ASSUME_TAC THENL
          [FIRST_ASSUM(fun th -> match concl th with
             Comb(Comb(_,l),Var("sx1",_)) when <l has word_join> -> SUBST1_TAC(SYM th) | _ -> NO_TAC)
           THEN REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_*] THEN CONV_TAC WORD_BLAST; ALL_TAC]
        NOTE: REABBREV_TAC stores the def as `<word_join> = sx1` (var on RHS), so match
        Var("sx1",_) on the RHS and SUBST1_TAC(SYM th), NOT on the LHS.
     B. pshuf1 = word_zx (usimd16 F (word_zx tab1))
        TACTIC (works): build F/target programmatically from the pshuf1 word_join def
        (extract g = word_zx(word_zx(word_subword f0sub(0,128))) via find_term), then
        SUBGOAL_THEN ... THENL [FIRST_ASSUM SUBST1_TAC(SYM <pshuf1 word_join def>) THEN
          REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_*;ARITH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC]

   *** BLOCKER for Step C (FIX NEEDED): the tab1 definition
       `word_zx(word_zx(read(memory:>bytes64(word_add table (word(8*<idx>)))) s13)) = tab1`
       was DROPPED by `PURGE_STALE_STATES_TAC ["s14"]` (step 14 area) / later purges,
       because it references s13. Without it, Step C (word_zx tab1 = PSHUFB control
       form via TABLE_VMOVQ_READ) cannot be done -- tab1 is now an unconstrained var.
       Also the table-read `...s13 = num_of_wordlist mldsa_rej_uniform_table` was purged
       (only s17's survives).
   FIX: BEFORE any PURGE that drops s13, capture tab1_eq in-context:
       - keep the s13 table-read (don't purge s13 until tab1_eq is established), OR
       - right after `REABBREV_TAC tab1 = read YMM6 s14` (step 14), derive
         tab1_eq : tab1 = word_zx(word_zx(word(num_of_wordlist(TABLE_ENTRY
           (word(val mask8 MOD 256)))))):int256
         via TABLE_VMOVQ_READ[table, val mask8 MOD 256, s13] (needs the s13 table-read +
         val mask8 MOD 256 < 256) + REWRITE_RULE[IDX_RED_ETA4] on tab1's def + GSYM,
         and ASSUME_TAC it (state-free: keyed on mask8/table only) so it survives PURGE.
       Then Step C's control form follows from tab1_eq (the word_zx-collapse via GSYM
       VAL_EQ + VAL_WORD_ZX_GEN + MOD_MOD_EXP_MIN, all in-context).
   With A,B,C done, the store value = SUBITER_STORE_POSTCOND's arg (g:=word_zx(word_zx
   (word_subword f0sub(0,128))), m:=word(val mask8 MOD 256)); apply it + REWRITE[SUBITER1_VALUE]
   + SUBITER_STORE_EXTEND. *)

(* === STEP C BLOCKER RESOLVED LIVE (2026-06-12) ============================
   The tab1_eq capture works when done right after `REABBREV_TAC tab1 = read YMM6 s14`
   and BEFORE purging s13. Exact live tactic (validated):
     (* reprove IDX_RED_ETA4 if not OCaml-bound -- it lives in main file but the
        let-name may not be in scope; reprove inline, it's tiny *)
     let asl = <goal asms> in
     let (_,tabdef) = find (\(_,t). tab1 def: word_zx(word_zx(read(bytes64 ...) s13)) = tab1) asl in
     let (_,tread13) = find (\(_,t). read(memory:>bytes(table,2048)) s13 = num_of_wordlist mldsa_rej_uniform_table) asl in
     let tvr = SPECL [`table`; `val mask8 MOD 256`; `s13`] TABLE_VMOVQ_READ in
     let rlt = prove(`val (mask8:int64) MOD 256 < 256`, ARITH_TAC) in
     let raw_eq = MP tvr (CONJ tread13 rlt) in
     let tabdef' = REWRITE_RULE[IDX_RED_ETA4] tabdef in
     let tab1_eq = GSYM(REWRITE_RULE[raw_eq] tabdef') in
     e(ASSUME_TAC tab1_eq);;
   RESULT (state-free, survives PURGE):
     tab1 = word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY (word (val mask8 MOD 256))))))
   With sx1=usimd8 (A), pshuf1=word_zx(usimd16 F (word_zx tab1)) (B), and tab1_eq,
   the store value rewrites (REWRITE[B] then REWRITE[tab1_eq, with word_zx-collapse])
   to SUBITER_STORE_POSTCOND's arg form with g=word_zx(word_zx(word_subword f0sub
   (0,128))), m=word(val mask8 MOD 256). NOTE: IDX_RED_ETA4 is in the main file
   but may need inline reproof if the OCaml let-name isn't in session scope. *)

(* === STEP B / tab1_eq INTERACTION (2026-06-12) ============================
   GOTCHA: once tab1_eq (tab1 = word_zx(word_zx(word(num_of_wordlist(TABLE_ENTRY
   (word(val mask8 MOD 256))))))) is an ASSUMPTION, the Step B SUBGOAL_THEN whose
   SIMP_TAC[...] runs over the goal will EXPAND `word_zx tab1` in the pshuf1
   word_join (LHS) to the triple-word_zx TABLE_ENTRY form, while the hand-built
   target RHS still says `word_zx tab1` -> control-width mismatch -> Step B leaves
   an open residual subgoal (2 subgoals).
   TWO clean fixes (pick one):
     (i) Do Step B (pshuf1 = word_zx(usimd16 F (word_zx tab1))) BEFORE capturing
         tab1_eq -- i.e. right after step 15 REABBREV pshuf1, while tab1 is still
         an opaque var. Then capture tab1_eq, then proceed. (Reorder.)
     (ii) Build Step B's target with the control already in TABLE_ENTRY form
         (substitute tab1_eq into the target's `word_zx tab1` -> the matching
         word_zx(word_zx(word_zx(word(num_of_wordlist(TABLE_ENTRY ...)))))), so
         both sides agree post-SIMP. Then the SUBITER_STORE_POSTCOND arg has
         m = word(val mask8 MOD 256) directly (no further tab1 rewrite needed).
   Fix (ii) is preferable: it lands pshuf1 in EXACTLY SUBITER_STORE_POSTCOND's
   expected shape (control = word_zx(word_zx(word(num_of_wordlist(TABLE_ENTRY m))))),
   so MATCH_MP SUBITER_STORE_POSTCOND applies with zero further massaging.
   STATE when stopped: at s17 (store done), A (sx1=usimd8) + tab1_eq both present
   as assumptions, single goal. Next: apply fix (ii) for Step B, then
   MATCH_MP SUBITER_STORE_POSTCOND (store256 fact) + REWRITE[SUBITER1_VALUE] +
   SUBITER_STORE_EXTEND for the sub-iter 1 memory postcondition. *)
