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
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`]) THEN
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
   bit 7 (word_subword f1bnd (8k,8)))) — moderate now (f1bnd opaque). REABBREV mask8. *)
e(X86_VSTEPS_TAC EXEC (11--11));;
e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM1 s10 = f1bnd:int256`]));;
e(REABBREV_TAC `mask8 = read R8 s11`);;
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

(* Step 13: movzbl r8b -> r10d.  Plain X86_STEPS (movzbl decodes fine; verbose VSTEPS does not
   fire on it).  R10 s13 = movzbl of mask8 = low byte; its structural value is needed later for
   the RAX bound at the mid-guard — that derivation is the next unit (use the s2n movzbl model
   read R10 s13 = word_zx(word_subword(word_zx (read R8 s12))(0,8)) + read R8 s12=mask8). *)
e(X86_STEPS_TAC EXEC (13--13));;
e(PURGE_STALE_STATES_TAC ["s12"]);;
(* probe checkpoint 4: at s13/pc+116. mask8 = word_zx(word(Sum_{k<32} 2^k bitval(bit 7
   (word_subword f1bnd (8k,8))))); R10 s13 = movzbl of mask8 = low 8 bits.  Both store hyps live. *)

(* Step 14: vmovq (tab,r10,8) -> ymm6.  YMM6 s14 = read(memory table + 8*r10) — the gather
   control vector table[mask&0xff] (small, 87 chars). *)
e(X86_VSTEPS_TAC EXEC (14--14));;
e(PURGE_STALE_STATES_TAC ["s13"]);;
(* probe checkpoint 5: at s14/pc+~. YMM6 = table[r10] control vector. *)

(* Step 15: vpshufb ymm6,xmm5(g0a)->ymm6.  YMM6 s15 = the s2n pshufb model output (8031 chars):
   per output lane = `if bit 7 (control byte) then word 0 else word_subword g0a (8*control,8)`
   where control bytes come from table[r10] = read(memory table+8*r10). This is exactly the
   form abstracted by PSHUFB_OUT_LIST g0a m / PSHUFB_OUT_BYTE. *)
e(X86_VSTEPS_TAC EXEC (15--15));;
e(PURGE_STALE_STATES_TAC ["s14"]);;
(* probe checkpoint 6: at s15. YMM6 = vpshufb(g0a, table[mask&0xff]).  NEXT: 16 vpmovsxbd
   ymm6->ymm1 (8 bytes sx -> 8 int32); 17 vmovdqu ymm1->(res,rax,4) STORE.
   To close the store value: the committed PSHUFB_ACCEPTED_PREFIX_NUM proves the first
   popcount(m) pshufb output bytes = MAP (\p. g0a.byte(8p,8)) (ACC_IDX m); compose with
   VPMOVSXBD_LANE_EXTRACT (byte->int32 sx) + the gather fact (g0a byte = word_sub 4 nibble) +
   SUBITER_STORE_SPEC to get stored list = REJ_SAMPLE_ETA4_BYTES[chunk0 bytes 0..3].
   Equivalently MATCH_MP_TAC SUBITER_STORE_SPEC (SPECL g0a, mask-byte) and discharge its 2 hyps
   from asm 28 (gather) + asm 29 (maskbit) via MASK_LOW_BIT. Then popcnt/RAX, mid-guard,
   sub-iters 2-4, jmp pc+56. *)

(* Step 16: vpmovsxbd ymm6->ymm1 (8 bytes sx -> 8 int32).  Step 17: vmovdqu ymm1->(res,rax,4)
   STORE — succeeds (RAX=word outlen0, outlen0<=248, so the bytes256 write at res+4*outlen0
   is in-bounds & nonoverlapping).  SUB-ITER 1 PIPELINE FULLY STEPPED THROUGH THE STORE in the
   actual CLEAN_BODY context. *)
e(X86_VSTEPS_TAC EXEC (16--16));;
e(X86_STEPS_TAC EXEC (17--17));;
e(PURGE_STALE_STATES_TAC ["s15";"s16"]);;
(* probe checkpoint 7: at s17/pc+136. Sub-iter 1 stored its int32 block at res+4*outlen0.
   The stored value = MAP word_sx (vpmovsxbd of vpshufb(g0a, table[mask&0xff])); by
   PSHUFB_ACCEPTED_PREFIX_NUM + VPMOVSXBD_LANE_EXTRACT + the proven gather/maskbit facts +
   SUBITER_STORE_SPEC it equals REJ_SAMPLE_ETA4_BYTES[chunk0 bytes 0..3].
   NEXT: popcnt r10d->r9d + add eax (RAX += popcount = +len of block) via
   RAX_BOUND_AFTER_POPCNT_ADD_DIRECT; shr r8d,8 (mask>>=8); add ecx,4 (RCX=16i+4); mid-guard
   ja (JA_NOT_TAKEN_LE + CLEAN_BLOCK_BOUNDS, no fire on clean iter); then sub-iters 2,3,4
   (vpsrldq/vextracti128 $1 for g, mask>>8/16/24, HI lemmas for 3,4); compose via
   REJ_SAMPLE_ETA4_BYTES_16_AS_4; add ecx,4 (final RCX=16(i+1)); jmp pc+56; ENSURES_FINAL_STATE. *)

(* Steps 18-21: popcnt r10d->r9d ; add eax,r9d ; shr r8d,8 ; add ecx,4.  CONFIRMED at s21/pc+156:
     read RCX s21 = word_zx(word_add(word_zx(word(16*i)))(word 4))            (= word(16i+4))
     read RAX s21 = word_zx(word_add(word_zx(word outlen0))(...word_popcount(word_zx r10v)...))
                    (= outlen0 + popcount(low byte of mask) = outlen0 + |accepted in block|)
     read R8  s21 = word_zx(word_ushr(word_zx mask8) 8)                       (mask >>= 8 for sub-iter 2)
     read R9  s21 = word_zx(word(word_popcount(word_zx r10v)))                (the block popcount)
     read RIP s21 = word(pc+156)                                             (cmp eax,248 mid-guard)
   The counter advances match the spec exactly. *)
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


