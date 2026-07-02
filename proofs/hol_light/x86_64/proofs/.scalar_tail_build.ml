(* Scalar-tail proof build file. Loaded after the main eta4 file + .scalar_tail_lemmas.ml.
   Builds: READ_1BYTE_EL, the per-byte loop body lemma, the WOP scalar-loop wrapper,
   and finally MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL (replacing the CHEAT). *)

(* Read one input byte at offset p from the buffer's num_of_wordlist contract. *)
let READ_1BYTE_EL = prove
 (`!(inlist:byte list) (buf:int64) (s:x86state) p n.
     LENGTH inlist = n /\ p < n /\
     read(memory :> bytes(buf, n)) s = num_of_wordlist inlist
     ==> read(memory :> bytes8 (word_add buf (word p))) s = EL p inlist`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inlist:byte list`; `p:num`] EL_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  SUBGOAL_THEN
   `read (bytes (word_add buf (word p),1)) (read memory s) =
    read (bytes (buf,n)) (read memory s) DIV 2 EXP (8 * p) MOD 256`
   SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_DIV] THEN
    MP_TAC(ISPECL [`word_add buf (word p):int64`; `n - p`; `1`; `read memory s:int64->byte`] READ_BYTES_MOD) THEN
    SUBGOAL_THEN `MIN (n - p) 1 = 1` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `MIN a 1 = 1 <=> 1 <= a`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `read (memory :> bytes (buf,n)) s = num_of_wordlist (inlist:byte list)` THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(256:num) = 2 EXP dimindex(:8)` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[WORD_MOD_SIZE]);;

(* jae(Condition_NB) fall-through: when a<k the unsigned >= jump is NOT taken.
   The model's flag condition is INT-typed (int_of_num &), NOT real — matching
   it requires the :int annotation (the classic invisible-type trap). Resolves
   the scalar-tail guards at pc+319 (256), pc+327 (272), pc+369/pc+383 (256). *)
let JAE_NOT_TAKEN_LT = prove
 (`!a k:num. a < k /\ k < 2 EXP 32
     ==> ~(&(val(word_zx(word a:int64):int32)):int - &k =
           &(val(word_sub(word_zx(word a:int64):int32) (word k):int32)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = a + 2 EXP 32 - k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word k:int32) = k` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; REFL_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a + 2 EXP 32 - k = (a + 2 EXP 32) - k /\ k <= a + 2 EXP 32` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&((a + 2 EXP 32) - k):int = &(a + 2 EXP 32) - &k` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ARITH_RULE `0 < 2 EXP 32`) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

(* jae(Condition_NB) TAKEN: when k<=a the unsigned >= jump IS taken (flag eq holds).
   Companion of JAE_NOT_TAKEN_LT for the nibble-reject branches (cmp r10d/r11d, 9). *)
let JAE_TAKEN_GE = prove
 (`!a k:num. k <= a /\ a < 2 EXP 32
     ==> (&(val(word_zx(word a:int64):int32)):int - &k =
          &(val(word_sub(word_zx(word a:int64):int32) (word k):int32)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = a - k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word k:int32) = k` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [REFL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(a - k):int = &a - &k` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REFL_TAC);;

(* Fast RIP-cond resolver: rewrites ONLY the RIP equation (a small term), not the
   whole eventually-goal — avoids the ~600s catastrophic whole-goal REWRITE. Finds
   the RIP=(if cond then..else..) assumption, the matching ~cond among assumptions
   (must be present and SAME-TYPED), and collapses via COND_CLAUSES. *)
let RESOLVE_RIP_FAST =
  W(fun (asl,_) ->
    let _,ripth = List.find (fun (_,th) -> let c=concl th in
        is_eq c && can (find_term (fun x->x=`RIP`)) c && can (find_term is_cond) c) asl in
    let p = fst(dest_cond(find_term is_cond (concl ripth))) in
    let negfact = snd(List.find (fun (_,th) -> aconv (concl th) (mk_neg p)) asl) in
    let resolved = REWRITE_RULE[negfact; COND_CLAUSES] ripth in
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> let c=concl th in
        is_eq c && can (find_term (fun x->x=`RIP`)) c && can (find_term is_cond) c)) THEN
    ASSUME_TAC resolved);;

(* ======================================================================== *)
(* Per-byte scalar-tail body lemma: one trip pc+314 -> pc+314, consuming    *)
(* input byte at position p, extending output by REJ_SAMPLE_ETA4_BYTES[b].   *)
(* Entry generalized to arbitrary p so the wrapper can iterate; the          *)
(* ~(L=255 /\ low<9) hypothesis rules out the mid-byte exit (handled by the  *)
(* terminal segment, not this looping body).                                 *)
(* ======================================================================== *)

(* Nibble-value bridge: the X86_VSTEPS-produced R10 expression (low nibble) after
   `mov r10d,r11d; and r10d,15` over the movzbl-loaded byte b, collapses to
   word(val b MOD 16):int64. The zx-tower shape (byte->int16->int32 widenings)
   is exactly what VSTEPS emits for the load + zero-extends. *)
let R10_NIBBLE_VAL = prove
 (`!b:byte. word_zx(word_and (word_zx (word_zx (word_zx (word_zx (word_zx b:int32):int64):int32):int64):int32) (word 15:int32)):int64 = word(val b MOD 16)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `(word 15:int32) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[VAL_WORD_ZX_GEN; VAL_WORD_AND_MASK_WORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
           VAL_WORD; ARITH] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b /\ val(b:byte) MOD 18446744073709551616 = val b`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(b:byte) MOD 16 < 18446744073709551616` ASSUME_TAC THENL
   [MP_TAC(SPECL[`val(b:byte)`;`16`] MOD_LT_EQ) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

(* High-nibble bridge: R11 after `shr r11d,4; and r11d,15` collapses to
   word(val b DIV 16):int64. Shape matches the X86_VSTEPS emission (ushr after a
   byte->int32->int64->int32 zx-tower, then 2 more zx, then and). *)
let R11_NIBBLE_VAL = prove
 (`!b:byte. word_zx (word_and (word_zx (word_zx (word_ushr (word_zx (word_zx (word_zx (b:byte) :int32) :int64) :int32) 4) :int64) :int32) (word 15 :int32)) :int64 = word (val b DIV 16)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `(word 15:int32) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[VAL_WORD_ZX_GEN; VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
           VAL_WORD; ARITH] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b /\ val(b:byte) MOD 18446744073709551616 = val b /\ (val(b:byte) DIV 16) MOD 18446744073709551616 = val b DIV 16 /\ (val(b:byte) DIV 16) MOD 4294967296 = val b DIV 16 /\ (val(b:byte) DIV 16) MOD 16 = val b DIV 16`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL[`val(b:byte)`;`16`] DIV_LT) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* RAX after `inc eax` over RAX=word L (L<256): the int32 inc widens back to word(L+1):int64. *)
let RAX_INC = prove
 (`!L. L < 256 ==> word_zx(word_add (word_zx (word L:int64):int32) (word 1:int32)):int64 = word(L+1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word L:int64):int32) = L` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val(word_zx(word_add (word_zx (word L:int64):int32) (word 1:int32)):int64) = L+1` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word_add (word_zx (word L:int64):int32) (word 1:int32)) = L + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_32] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `val(word_add (word_zx (word L:int64):int32) (word 1:int32))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_ZX THEN REWRITE_TAC[DIMINDEX_32;DIMINDEX_64] THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

(* Store-value bridges: the scalar tail computes `4 - nibble` as int32 then the
   model wraps it in word_zx(word_zx(...)) (32->64->32 round trip) at the vmovd/store.
   For accepted nibbles (<9) this equals the spec coefficient word_sx(word_sub(word 4:int16)..).
   Proved by enumerating the 9 accepted nibble values + WORD_BLAST. *)
let LO_STORE_VAL = prove
 (`!b:byte. val b MOD 16 < 9
   ==> word_zx(word_zx(word_sub (word 4:int32) (word_zx(word(val b MOD 16):int64):int32):int32):int64):int32 =
       word_sx(word_sub (word 4:int16) (word(val b MOD 16):int16):int16):int32`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(b:byte) MOD 16 = 0 \/ val b MOD 16 = 1 \/ val b MOD 16 = 2 \/ val b MOD 16 = 3 \/
                val b MOD 16 = 4 \/ val b MOD 16 = 5 \/ val b MOD 16 = 6 \/ val b MOD 16 = 7 \/ val b MOD 16 = 8`
   MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST);;

let HI_STORE_VAL = prove
 (`!b:byte. val b DIV 16 < 9
   ==> word_zx(word_zx(word_sub (word 4:int32) (word_zx(word(val b DIV 16):int64):int32):int32):int64):int32 =
       word_sx(word_sub (word 4:int16) (word(val b DIV 16):int16):int16):int32`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(b:byte) DIV 16 = 0 \/ val b DIV 16 = 1 \/ val b DIV 16 = 2 \/ val b DIV 16 = 3 \/
                val b DIV 16 = 4 \/ val b DIV 16 = 5 \/ val b DIV 16 = 6 \/ val b DIV 16 = 7 \/ val b DIV 16 = 8`
   MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST);;

(* Per-byte output-length step lemmas, one per nibble-acceptance combination.
   Drive the loop invariant's RAX update (LENGTH outlist grows by 0/1/2). *)
let LEN_STEP_BOTH = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 9 /\ val(EL p inlist) DIV 16 < 9
   ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) + 2`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_LO = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 9 /\ ~(val(EL p inlist) DIV 16 < 9)
   ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) + 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_HI = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 9) /\ val(EL p inlist) DIV 16 < 9
   ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) + 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_NONE = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 9) /\ ~(val(EL p inlist) DIV 16 < 9)
   ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Per-byte output-list APPEND step, one per acceptance combination.
   Used in the body lemma's memory fold: REJ(SUB(0,p+1)) = APPEND (REJ(SUB(0,p))) <new coeffs>. *)
let REJ_STEP_BOTH = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 9 /\ val(EL p inlist) DIV 16 < 9
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 4:int16) (word(val(EL p inlist) MOD 16))):int32;
               word_sx(word_sub (word 4:int16) (word(val(EL p inlist) DIV 16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA4_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA4_BYTES_1_BOTH THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_LO = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 9 /\ ~(val(EL p inlist) DIV 16 < 9)
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 4:int16) (word(val(EL p inlist) MOD 16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA4_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA4_BYTES_1_LOW_ONLY THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_HI = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 9) /\ val(EL p inlist) DIV 16 < 9
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 4:int16) (word(val(EL p inlist) DIV 16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA4_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA4_BYTES_1_HIGH_ONLY THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_NONE = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 9) /\ ~(val(EL p inlist) DIV 16 < 9)
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA4_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES [EL p (inlist:byte list)] = []` SUBST1_TAC THENL
   [MATCH_MP_TAC REJ_SAMPLE_ETA4_BYTES_1_REJECT_BOTH THEN ASM_REWRITE_TAC[]; REWRITE_TAC[APPEND_NIL]]);;

(* Output-length step bounds for the WOP wrapper: per byte, outlen grows by 0..2. *)
let OUTLEN_STEP_LE2 = prove
 (`!(inlist:byte list) k. k < LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k+1) inlist):int32 list) <=
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k) inlist):int32 list) + 2`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`k:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let OUTLEN_STEP_GE = prove
 (`!(inlist:byte list) k. k < LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k) inlist):int32 list) <=
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k+1) inlist):int32 list)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`k:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Count-exit cap lemmas for the WOP wrapper terminal case (outlen >= 256). *)
(* Spec side: SUB_LIST(0,256) of full REJ = SUB_LIST(0,256) of any prefix whose
   output already reached >=256 elements. *)
let SUB_LIST_256_PREFIX_GE = prove
 (`!(inlist:byte list) k.
     k <= LENGTH inlist /\
     256 <= LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k) inlist):int32 list)
     ==> SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist :int32 list) =
         SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k) inlist))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `inlist:byte list`] REJ_SAMPLE_ETA4_SUB_LIST_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ext:int32 list` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th])) THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

(* Memory side: if res holds list L (len>=256), bytes(res,4*256) holds SUB_LIST(0,256) L. *)
let MEM_PREFIX_256 = prove
 (`!res (s:x86state) (L:int32 list).
     256 <= LENGTH L /\
     read(memory :> bytes(res, 4 * LENGTH L)) s = num_of_wordlist L
     ==> read(memory :> bytes(res, 4 * 256)) s = num_of_wordlist(SUB_LIST(0,256) L)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `pre = SUB_LIST(0,256) (L:int32 list)` THEN
  ABBREV_TAC `suf = SUB_LIST(256, LENGTH(L:int32 list) - 256) L` THEN
  SUBGOAL_THEN `(L:int32 list) = APPEND pre suf` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pre";"suf"] THEN
    MP_TAC(ISPECL [`L:int32 list`; `256`; `LENGTH(L:int32 list) - 256`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN ASM_SIMP_TAC[ARITH_RULE `256 <= n ==> 256 + (n - 256) = n`] THEN
    REWRITE_TAC[SUB_LIST_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(pre:int32 list) = 256` ASSUME_TAC THENL
   [EXPAND_TAC "pre" THEN REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `read(memory :> bytes(res, 4 * LENGTH (L:int32 list))) s = num_of_wordlist L` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ASSUME `(L:int32 list) = APPEND pre suf`] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN
  MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s:x86state`;
     `pre:int32 list`; `suf:int32 list`; `4*256`; `4 * LENGTH(suf:int32 list)`]
     BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  ASM_REWRITE_TAC[DIMINDEX_32; ARITH_RULE `32 * 256 = 8 * (4 * 256)`] THEN
  REWRITE_TAC[ARITH_RULE `4 * 256 + 4 * s = 4 * (256 + s)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[]);;
