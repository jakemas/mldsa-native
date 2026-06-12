(* ============================================================================
   CLEAN_BODY full proof build (2026-06-12). Run via loadt AFTER the main file
   is loaded (it uses EXEC, the store lemmas, SUBITER_STORE_SPEC, etc.).
   Non-interactive: either proves MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY or fails at
   the first bad tactic. Assembled from the validated interactive session.
   ============================================================================ *)

let EXEC = MLDSA_REJ_UNIFORM_ETA4_EXEC;;

let PURGE_STALE_STATES_TAC names =
  let rec refs_stale tm = match tm with
    | Comb(Comb(Const("read",_),_),Var(nm,_)) when List.mem nm names -> true
    | Comb(a,b) -> refs_stale a || refs_stale b | Abs(_,b) -> refs_stale b | _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th -> if refs_stale (concl th) then ALL_TAC else failwith "keep"));;

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
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[OP8_R8B_READ] THENC ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV));;

let DROP_WORDJOIN_TAC : tactic = fun (asl,w) ->
  (REPEAT(FIRST_X_ASSUM(fun th ->
     if can (find_term (fun u -> match u with Const("word_join",_) -> true | _ -> false)) (concl th)
     then ALL_TAC else failwith "keep"))) (asl,w);;

let wzx_id = prove(`!x:int128. word_zx x:int128 = x`, REWRITE_TAC[WORD_ZX_TRIVIAL]);;
let exp8 = prove(`(256:num) = 2 EXP 8`, CONV_TAC NUM_REDUCE_CONV);;

let IDX_RED_ETA4 = prove
 (`val (word_zx (word_zx (word (val (mask8:int64) MOD 256):byte):int32):int64) = val mask8 MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD] THEN SIMP_TAC[DIMINDEX_64;DIMINDEX_32;DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SUBGOAL_THEN `val (mask8:int64) MOD 256 < 256` ASSUME_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 256 /\ n < 4294967296 /\ n < 18446744073709551616`]]);;

let wzx256 = prove(`!x:int256. word_zx x:int256 = x`, REWRITE_TAC[WORD_ZX_TRIVIAL]);;

(* ===========================================================================
   WIDE per-byte gather / mask foralls (j<32), proven from the committed
   F0SUB_BYTES(_HI) / F1BND_BYTES(_HI) via EXPAND_CASES_CONV (NOT a big-disjunction
   ARITH_RULE, which hangs on Presburger blowup beyond 8 disjuncts).  These cover
   ALL 32 byte lanes of f0sub/f1bnd, so ALL 4 sub-iters' SUBITER_STORE_SPEC gather
   / maskbit hyps are instances (after the per-lane WORD_SUBWORD_SUBWORD merge).
   Stated on the BARE simd2 form (= F0SUB_BYTES's form); in the body the stepped
   vpsubb word_join is folded to this simd2 form by GSYM(REWRITE_CONV[simd2;simd16]
   THENC DEPTH BETA).  ETA const = word 1816..., BOUND const = word 4086... .
   =========================================================================== *)

let GATHER_WIDE = prove
 (`!ff:int256. !j. j < 32 ==>
     word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
       (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (ff:int256))
       (8*j,8):byte
     = word_sub (word 4) (word_subword (ff:int256) (8*j,8):byte)`,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[F0SUB_BYTES; F0SUB_BYTES_HI]);;

let MASK_WIDE = prove
 (`!fn:int256. (!k. k < 32 ==> val(word_subword fn (8*k,8):byte) < 16) ==>
     !k. k < 32 ==>
       (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
          (fn:int256)
          (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (8*k,8):byte)
        <=> val(word_subword fn (8*k,8):byte) < 9)`,
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[F1BND_BYTES; F1BND_BYTES_HI] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC VPSUBB_SIGN_BIT_LT_9 THEN
  W(fun (asl,w) ->
     let off = dest_small_numeral(fst(dest_pair(rand(rand(lhand w))))) in
     let bnd = find (fun (_,th) -> is_forall(concl th) && can(find_term(fun u->u=`16`))(concl th)) asl in
     MP_TAC(CONV_RULE NUM_REDUCE_CONV (MP (SPEC (mk_small_numeral(off/8)) (snd bnd))
              (EQT_ELIM(NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral(off/8)) `32`))))) THEN
     CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN ACCEPT_TAC));;

(* The conv that expands a bare simd2 (eta/bound subtract over fn) to the word_join
   form the simulator (x86_VPSUBB_ALT) produces.  GSYM of (this conv applied to the
   bare simd2) folds the stepped word_join BACK to the bare simd2, so GATHER_WIDE /
   MASK_WIDE then apply.  VALIDATED 2026-06-12: from the fully-expanded word_join,
   REWRITE[GSYM(SIMD2_EXPAND_CONV bare)] THEN MP_TAC(SPECL[fn;j]GATHER_WIDE) closes a
   gather lane in 0.01s.  In the body, build `bare` = the simd2 with the live fn, take
   the foldback = GSYM(SIMD2_EXPAND_CONV bare), and rewrite the stepped read-eq.
   NOTE: the stepped read YMM0 s10 may carry word_zx wrappers / unreduced dimindex;
   reconcile by also REWRITE[wzx256] + the dimindex reductions when matching. *)
let SIMD2_EXPAND_CONV : conv =
  REWRITE_CONV[simd2;simd16] THENC DEPTH_CONV(GEN_BETA_CONV ORELSEC BETA_CONV);;

Printf.printf "CLEAN_BODY_BUILD: helpers + GATHER_WIDE + MASK_WIDE + SIMD2_EXPAND_CONV defined\n";;

let F0NIB_CHUNK0 =
  `word_and (word_or (usimd16 (\b:byte. word_zx b:int16) chunk0:int256)
                     (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) chunk0:int256):int256))
            (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)`;;

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

(* ---- DIAGNOSTIC build: prologue + SIMD setup -> s10, print the stepped f0sub/f1bnd
   forms so the in-body simd2-fold can be matched exactly. This prove() is deliberately
   left to fail (NO_TAC after the print) -- it's a probe, not the final proof. ---- *)
let _ = (try prove(clean_body_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  FIRST_ASSUM(fun th -> if concl th =
      `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) else NO_TAC) THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  VAL_INT64_TAC `outlen0:num` THEN
  X86_STEPS_TAC EXEC (1--2) THEN
  SUBGOAL_THEN `read RIP s2 = word(pc + 67):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 318`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (3--4) THEN
  SUBGOAL_THEN `read RIP s4 = word(pc + 79):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&256:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 318`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC EXEC (5--5) THEN
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `16*i <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(16*i):int64) = 16*i`; ARITH_RULE `1 * x = x`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read (memory :> bytes128 (word_add buf (word (16 * i)))) s4 = chunk0`]) THEN
  SUBGOAL_THEN `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s5`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256`]) THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM2 s5 =
    word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256`]) THEN
  SUBGOAL_THEN (mk_eq(`read YMM0 s8:int256`, F0NIB_CHUNK0)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s8`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s5";"s6";"s7"] THEN
  ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES) THEN
  ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES_HI) THEN
  ABBREV_TAC `fn:int256 = read YMM0 s8` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME(mk_eq(`fn:int256`, F0NIB_CHUNK0)))]) THEN
  X86_VSTEPS_TAC EXEC (9--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s8 = fn:int256`;
     ASSUME `read YMM4 s8 = word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256`]) THEN
  ABBREV_TAC `f1bnd:int256 = read YMM1 s9` THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s9 = fn:int256`;
     ASSUME `read YMM3 s9 = word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256`]) THEN
  ABBREV_TAC `f0sub:int256 = read YMM0 s10` THEN
  W(fun (asl,w) ->
     let f0d = find (fun (_,th) -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) asl in
     let rhs0 = rand(concl(snd f0d)) in
     (* try the in-body fold: does GSYM(SIMD2_EXPAND_CONV bare) match the stepped f0sub? *)
     let bare = `simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
                   (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (fn:int256)` in
     let expanded = rand(concl(SIMD2_EXPAND_CONV bare)) in
     ignore expanded;
     (* The stepped f0sub is chunk0-direct word_join. Test wide gather forall via
        JOIN extract + EXPAND_CASES over the stepped f0sub def.  Target byte 8j =
        word_sub(word 4)(word(val(word_subword chunk0 (8*(j/2),8)) MOD-if-even/DIV-if-odd 16)).
        Use the f0sub DEF (rhs0) so JOIN extract works; the leaf value comes out as
        REWRITE reduces. Prove `!j. j<32 ==> word_subword f0sub (8j,8) = word_subword rhs0 (8j,8)`
        is trivial via the f0sub def; the real test is reducing rhs0's lane via JOIN. *)
     let f0d = snd(find (fun (_,th) -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) asl) in
     let t0 = Sys.time() in
     (* reduce lane 20 (offset 160) of f0sub via JOIN extract; print whatever it becomes *)
     let res =
       (try
          let red = (REWRITE_CONV[f0d] THENC
                ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                REPEATC(CHANGED_CONV(SIMP_CONV[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                  DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THENC
                  NUM_REDUCE_CONV)) THENC
                TRY_CONV(REWRITE_CONV[WORD_SUBWORD_BYTE_ID]))
               `word_subword (f0sub:int256) (8*20,8):byte` in
          string_of_term(rand(concl red))
        with e -> "RED EXC: "^Printexc.to_string e) in
     let oc = open_out "/tmp/f0sub_form.txt" in
     output_string oc (Printf.sprintf "lane20 reduced in %.2fs to:\n%s\n" (Sys.time()-.t0) res);
     close_out oc;
     NO_TAC)) with e -> Printf.printf "(probe ended: %s)\n" (Printexc.to_string e); REFL `T`);;

Printf.printf "DIAGNOSTIC_DONE (reaches s10, f0sub chunk0-direct)\n";;
