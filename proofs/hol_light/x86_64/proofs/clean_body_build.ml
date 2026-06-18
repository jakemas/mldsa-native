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

(* ZZCOLLAPSE / LACC8: reproved inline (the main-file let-names aren't in session scope). *)
let ZZCOLLAPSE = prove
 (`!(X:int128) j. j < 8
    ==> word_subword (word_zx (word_zx X:int256):int128) (8*j,8):byte = word_subword X (8*j,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_zx (X:int128):int256`;`8*j`;`8`]
    (INST_TYPE[`:128`,`:N`;`:256`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  MP_TAC(ISPECL [`X:int128`;`8*j`;`8`]
    (INST_TYPE[`:256`,`:N`;`:128`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_128;DIMINDEX_256] THEN
  SUBGOAL_THEN `MIN (8*j+8) 128 <= 256 /\ MIN (8*j+8) 256 <= 128` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> REWRITE_TAC[th2;th1]))]);;

let LACC8 = prove(`!m:byte. LENGTH(ACC_IDX m) <= 8`,
  GEN_TAC THEN REWRITE_TAC[ACC_IDX] THEN
  MP_TAC(ISPECL [`\i. bit i (m:byte)`; `[0;1;2;3;4;5;6;7]:num list`] LENGTH_FILTER) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* LEN_RECONCILE: given the maskbit correspondence (the maskbit_tgt form), the accept count
   LENGTH(ACC_IDX m) equals LENGTH(REJ_SAMPLE_ETA4_BYTES[chunk0 block]) — needed to retype the
   block-store width (4*LENGTH(ACC_IDX m)) as (4*LENGTH(REJ_SAMPLE block)) for SUBITER_STORE_EXTEND. *)
let LEN_RECONCILE = prove
 (`!(m:byte) (chunk0:int128).
     (!j. j < 8 ==> (bit j m <=>
        EL j [val(word_subword chunk0 (0,8):byte) MOD 16; val(word_subword chunk0 (0,8):byte) DIV 16;
              val(word_subword chunk0 (8,8):byte) MOD 16; val(word_subword chunk0 (8,8):byte) DIV 16;
              val(word_subword chunk0 (16,8):byte) MOD 16; val(word_subword chunk0 (16,8):byte) DIV 16;
              val(word_subword chunk0 (24,8):byte) MOD 16; val(word_subword chunk0 (24,8):byte) DIV 16] < 9))
     ==> LENGTH(ACC_IDX m) =
         LENGTH(REJ_SAMPLE_ETA4_BYTES [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
                                       word_subword chunk0 (16,8); word_subword chunk0 (24,8)]:int32 list)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:byte`;
    `word(val(word_subword (chunk0:int128) (0,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (0,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (8,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (8,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (16,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (16,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (24,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (24,8):byte) DIV 16):byte`] ACC_LENGTH_EQ_FILTER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(fun (asl,gw) -> let n = rand(rator(lhand gw)) in
       MP_TAC(SPEC n (find (fun th -> is_forall(concl th) && can(find_term(fun u->match u with Const("EL",_)->true|_->false))(concl th)) (map snd asl)))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    W(fun (asl,gw) -> let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" && type_of u=`:byte` with _->false) gw in
       MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN STRIP_TAC THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       REFL_TAC);
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LENGTH_FILTER_BYTE_NIBBLES_4_BYTES; LENGTH_REJ_SAMPLE_ETA4_BYTES]]);;

(* SUBITER_FOLD_STEP: reusable fold of one sub-iter's REJ block onto the running prefix.
   Given (a) the accept-count = block length [from LEN_RECONCILE], (b) the prefix store
   read(bytes(res, 4*LEN(REJ prefixbytes))) = nwl(REJ prefixbytes), and (c) this sub-iter's
   block store read(bytes(res + 4*LEN(REJ prefixbytes), 4*LEN(ACC_IDX m))) = nwl(REJ blk),
   conclude read(bytes(res, 4*LEN(REJ (prefixbytes++blk)))) = nwl(REJ (prefixbytes++blk)).
   Applies identically to all 4 sub-iters (prefixbytes = SUB_LIST(0,16i+4k), blk = next 4 bytes).
   Pair with REJ_PREFIX_STEP_4 (below) to turn prefixbytes++blk back into SUB_LIST(0,16i+4(k+1)). *)
let SUBITER_FOLD_STEP = prove
 (`!res s (m:byte) (blk:byte list) (prefixbytes:byte list).
     LENGTH(ACC_IDX m) = LENGTH(REJ_SAMPLE_ETA4_BYTES blk:int32 list) /\
     read(memory:>bytes(res, 4*LENGTH(REJ_SAMPLE_ETA4_BYTES prefixbytes:int32 list))) s =
       num_of_wordlist(REJ_SAMPLE_ETA4_BYTES prefixbytes) /\
     read(memory:>bytes(word_add res (word(4*LENGTH(REJ_SAMPLE_ETA4_BYTES prefixbytes:int32 list))),
                        4*LENGTH(ACC_IDX m))) s =
       num_of_wordlist(REJ_SAMPLE_ETA4_BYTES blk)
     ==> read(memory:>bytes(res, 4*LENGTH(REJ_SAMPLE_ETA4_BYTES(APPEND prefixbytes blk):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(APPEND prefixbytes blk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`res:int64`; `s:x86state`;
                 `REJ_SAMPLE_ETA4_BYTES prefixbytes:int32 list`;
                 `REJ_SAMPLE_ETA4_BYTES blk:int32 list`] SUBITER_STORE_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if can(find_term(fun u->u=`ACC_IDX (m:byte)`)) (concl th)
                            then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND; LENGTH_APPEND;
                ARITH_RULE `4*a+4*b = 4*(a+b)`]]);;

(* REJ_PREFIX_STEP_4: SUB_LIST(0,16i+4k) ++ SUB_LIST(16i+4k,4) = SUB_LIST(0,16i+4(k+1)) at the
   REJ_SAMPLE level. After SUBITER_FOLD_STEP yields nwl(REJ(SUB_LIST(0,n) ++ SUB_LIST(n,4))),
   rewrite by GSYM REJ_PREFIX_STEP_4 (with n = 16i+4k) back to nwl(REJ(SUB_LIST(0,n+4))). *)
let REJ_PREFIX_STEP_4 = prove
 (`!(inlist:byte list) n.
     REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0, n+4) inlist):int32 list =
     APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,n) inlist))
            (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (n,4) inlist))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`n:num`;`4`;`0`] SUB_LIST_SPLIT);
              REJ_SAMPLE_ETA4_BYTES_APPEND]);;

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

(* maskbit_tgt / pf_target / MASKBIT_PF_TAC: baked in so the file is self-contained
   (previously session-only, which broke deterministic reload). maskbit_tgt is the
   sub-iter-1 VPMOVMSKB-byte <-> nibble-accept correspondence in the EL-list form
   LEN_RECONCILE consumes; pf_target is the pshufb lane form (= read YMM6 s15) matching
   SUBITER_STORE_POSTCOND's usimd16/TABLE_ENTRY control; MASKBIT_PF_TAC discharges
   maskbit_tgt in-context (SUM32 = SUM8 + 256*HIGH split, val mask8 = SUM32 MOD 2^32,
   MASK_LOW_BIT per-lane, VPSUBB_SIGN_BIT_LT_9). *)
let maskbit_tgt =
  `!j. j < 8 ==> (bit j (word (val (mask8:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (0,8):byte) MOD 16;
         val(word_subword chunk0 (0,8):byte) DIV 16; val(word_subword chunk0 (8,8):byte) MOD 16;
         val(word_subword chunk0 (8,8):byte) DIV 16; val(word_subword chunk0 (16,8):byte) MOD 16;
         val(word_subword chunk0 (16,8):byte) DIV 16; val(word_subword chunk0 (24,8):byte) MOD 16;
         val(word_subword chunk0 (24,8):byte) DIV 16] < 9)`;;

let pf_target =
  `pshuf1:int256 =
   word_zx
   (usimd16
    (\i:byte. if bit 7 i
         then word 0:byte
         else word_subword (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128)
              (8 * val (word_subword i (0,4):4 word),8):byte)
   (word_zx
   (word_zx (word (num_of_wordlist (TABLE_ENTRY (word (val (mask8:int64) MOD 256):byte))):int64):int128):int128):int128)`;;

let MASKBIT_PF_TAC : tactic =
  W(fun (asl,w) ->
    let m8 = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) (map snd asl) in
    let sum32 = rand(rand(lhand(concl m8))) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let sum8 = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (List.map2 (fun wt bv -> if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) [1;2;4;8;16;32;64;128] (map (fun i->List.nth bvs i) (0--7))) in
    let high = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (map (fun i -> let wt = 1 lsl (i-8) in if wt=1 then List.nth bvs i else mk_binop `( * ):num->num->num` (mk_small_numeral wt) (List.nth bvs i)) (8--31)) in
    let splitth = prove(mk_eq(sum32, mk_binop `(+):num->num->num` sum8 (mk_binop `( * ):num->num->num` `256` high)), ARITH_TAC) in
    let byteeq32 = TRANS (AP_TERM `word:num->byte` splitth) (SPECL [sum8; high] WORD_ADD_256_BYTE) in
    let beq = mk_eq(`word (val (mask8:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8)) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (0--7) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(`val (mask8:int64)`, mk_binop `MOD` sum32 `2 EXP 32`)) SUBST1_TAC THENL
       [SUBST1_TAC(SYM m8) THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
        MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [sum32; `2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_binop `MOD` (mk_binop `MOD` sum32 `2 EXP 32`) `256`, mk_binop `MOD` sum32 `256`)) SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV); ALL_TAC] THEN
      REWRITE_TAC[WORD_BYTE_MOD] THEN ACCEPT_TAC byteeq32;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
             DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
      CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    W(fun (asl2,w2) ->
       let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
         type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
       MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN STRIP_TAC THEN
       ASM_SIMP_TAC[VPSUBB_SIGN_BIT_LT_9; VAL_WORD_EQ; DIMINDEX_8;
         ARITH_RULE `n < 256 ==> n MOD 16 < 256`; ARITH_RULE `n < 256 ==> n DIV 16 < 256`;
         ARITH_RULE `n < 256 ==> n MOD 16 < 16`; ARITH_RULE `n < 256 ==> n DIV 16 < 16`]));;

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

(* Byte-value helper lemmas for the sub-iter store-value bitsum reductions. *)
let VAL_WORD_BYTE_LT256 = prove
 (`!n. n < 256 ==> val(word n:byte) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;
let BYTE_DIV16_LT = prove
 (`!b:byte. val b DIV 16 < 256`,
  GEN_TAC THEN MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC `b:byte` VAL_BOUND)) THEN ARITH_TAC);;
let BYTE_MOD16_LT = prove
 (`!b:byte. val b MOD 16 < 256`,
  GEN_TAC THEN MP_TAC(SPECL[`val(b:byte)`;`16`] MOD_LT_EQ) THEN ARITH_TAC);;

Printf.printf "ABOUT_TO_PROVE\n";;
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
  (* MASKBIT forall derived NOW (f1bnd word_join def still present): bit 7(f1bnd lane k) <=>
     EL k[chunk0 nibbles]<9. ASSUME it — survives the DROP below + downstream purges. Used by
     counter stage 3b. (Probe proves this SUBGOAL before its DROP, lines 216-237.) *)
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      (* prove `f1bnd = wj ==> (!k...)` as a CLOSED implication (f1d discharged as antecedent,
         so the result has NO extra hyps), then MP with f1d. The DISCH'd eq is used to rewrite. *)
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*k,8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (0,8):byte) MOD 16; val(word_subword chunk0 (0,8):byte) DIV 16;
                  val(word_subword chunk0 (8,8):byte) MOD 16; val(word_subword chunk0 (8,8):byte) DIV 16;
                  val(word_subword chunk0 (16,8):byte) MOD 16; val(word_subword chunk0 (16,8):byte) DIV 16;
                  val(word_subword chunk0 (24,8):byte) MOD 16; val(word_subword chunk0 (24,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  (fun g -> (let oc=open_out "/tmp/cs_mb.txt" in output_string oc "early maskbit assumed"; close_out oc); ALL_TAC g) THEN
  (* DROP f0sub/f1bnd word_join defs BEFORE vpmovmskb (s11) — mirrors the probe (clean_body_probe.ml
     lines 243-245). This keeps R8/R9's vpmovmskb+popcount over the OPAQUE `f1bnd` var (via the
     `read YMM1 s10 = f1bnd` fold) instead of the expanded word_join, so stage d's popeq / low8 /
     BOOL_CASES (over `word_subword f1bnd (8k,8)`) match the popcount term. Without this, R9 s21 =
     popcount(...word_join expanded...) and stage d leaves unsolved goals. *)
  REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && (lhand(concl th) = `f0sub:int256` || lhand(concl th) = `f1bnd:int256`)
     then ALL_TAC else failwith "keep")) THEN
  (* ---- STEP s11-s17 FIRST (vpmovmskb, vextracti128, movzbl R10 capture, vmovq, vpshufb,
     vpmovsxbd, vmovdqu store), keeping f0sub/f1bnd defs. The gather/mask SUBGOALs are proven
     AFTER stepping: their `EL j [...]`-shaped assumptions confuse X86_VSTEPS' simulator
     (vextracti128 at s12 fails with "mk_comb: types do not agree" if they're in context). ---- *)
  X86_VSTEPS_TAC EXEC (11--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM1 s10 = f1bnd:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s10"] THEN
  X86_VSTEPS_TAC EXEC (12--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s11 = f0sub:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s11"] THEN
  REABBREV_TAC `mask8 = read R8 s12` THEN
  X86_VERBOSE_STEP_TAC EXEC "s13" THEN
  MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s12 = mask8:int64`]) THEN
  X86_VSTEPS_TAC EXEC (14--14) THEN REABBREV_TAC `tab1 = read YMM6 s14` THEN
  X86_VSTEPS_TAC EXEC (15--15) THEN REABBREV_TAC `pshuf1 = read YMM6 s15` THEN
  PURGE_STALE_STATES_TAC ["s14"] THEN
  X86_VSTEPS_TAC EXEC (16--16) THEN REABBREV_TAC `sx1 = read YMM1 s16` THEN
  (* stepA: establish sx1 = usimd8 word_sx (word_zx(word_zx pshuf1)) (the vpmovsxbd lane form). *)
  SUBGOAL_THEN `sx1:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf1:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx1def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx1:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx1def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  PURGE_STALE_STATES_TAC ["s15"] THEN
  X86_STEPS_TAC EXEC (17--17) THEN
  PURGE_STALE_STATES_TAC ["s16"] THEN
  (fun g -> (let oc=open_out "/tmp/cs_s17.txt" in output_string oc "reached s17 (store done)"; close_out oc); ALL_TAC g) THEN
  X86_STEPS_TAC EXEC (18--21) THEN
  (fun g -> (let oc=open_out "/tmp/cs_c1821.txt" in output_string oc "counters 18-21 done"; close_out oc); ALL_TAC g) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 272` THEN
    UNDISCH_TAC `16 * i <= 256` THEN ARITH_TAC; STRIP_TAC] THEN
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM m8def])) THEN
  (* === REORDERED branch resolution (NO RULE_ASSUM over s21 state) === *)
  W(fun (asl,w) ->
    (* 1. popeq: word_popcount(word_zx^3(word(val mask8 MOD 256))) = bitsum8(low8 of f1bnd) *)
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s21",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    (* 2. bitsum8 = LENGTH(REJ_NIBBLES block0) via maskbit forall + block byte facts *)
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c) asl) in
    let mb_tm = concl maskbit in
    let mb_assumed = ASSUME mb_tm in
    let mbits = map (fun k -> let th=SPEC(mk_small_numeral k) mb_assumed in
         CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    (* combined: word_popcount(...) = LENGTH(REJ_NIBBLES block0) *)
    let pop_len = TRANS popeq bsum in
    (* 3. bound: outlen0 + LENGTH(REJ_NIBBLES block0) <= 248 *)
    let leninl = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asl in
    let i116 = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asl in
    let nible = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA4",_),_))),_) -> true | _ -> false) asl in
    let len_eq = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asl in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=256 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`)
                    (snd i116)) (snd leninl) in
    let bnd0 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_1) (CONJ a1 (snd nible)) in
    let bnd = REWRITE_RULE[snd len_eq] bnd0 in  (* outlen0 + LENGTH(REJ_NIBBLES block0) <= 248 *)
    (* 4. RAX collapse: word_zx(word_add(word_zx(word outlen0))(word_zx(word_zx(word popcount)))) = word(outlen0+block0len) *)
    let block0len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in  (* word_zx(...word outlen0...word block0len...) = word(outlen0+block0len) *)
    (* but RAX has popcount, not block0len; rewrite popcount->block0len first via pop_len *)
    let rax_red = REWRITE_RULE[pop_len] (GSYM(REWRITE_RULE[GSYM pop_len] (SYM rax_red0))) in
    (* JA_NOT_TAKEN: outlen0+block0len <= 248 *)
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `outlen0:num` block0len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    (let oc=open_out "/tmp/reorder_facts.txt" in
     output_string oc ("pop_len: "^string_of_term(concl pop_len)^"\n\nrax_red0: "^string_of_term(concl rax_red0)^
       "\n\nja: "^string_of_term(concl ja)^"\n\nbnd: "^string_of_term(concl bnd)^"\n"); close_out oc);
    (* stash these as assumptions for the step *)
    ASSUME_TAC pop_len THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (22--23) THEN
  (* resolve the ja branch: RIP s23 = pc+167 (fall through to sub-iter 2) *)
  SUBGOAL_THEN `read RIP s23 = word (pc + 167):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th)) asl in
      FIRST_ASSUM(fun th -> if can(find_term(fun u->u=`pc + 167`))(concl th) then MP_TAC th else NO_TAC) THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < 8 ==>
      word_subword (word_subword (f0sub:int256) (0,128):int128) (8*j,8):byte =
      word_sub (word 4) (word(EL j [val(word_subword (chunk0:int128) (0,8):byte) MOD 16;
         val(word_subword chunk0 (0,8):byte) DIV 16; val(word_subword chunk0 (8,8):byte) MOD 16;
         val(word_subword chunk0 (8,8):byte) DIV 16; val(word_subword chunk0 (16,8):byte) MOD 16;
         val(word_subword chunk0 (16,8):byte) DIV 16; val(word_subword chunk0 (24,8):byte) MOD 16;
         val(word_subword chunk0 (24,8):byte) DIV 16]):byte)`
   (fun bg ->
    SUBGOAL_THEN maskbit_tgt (fun mthm ->
     SUBGOAL_THEN pf_target (fun pfth ->
      W(fun (asl,w) ->
        let asms = map snd asl in
        (* the store at s23 already has RHS = usimd8 form (stepA's sx1=usimd8 was auto-applied). *)
        let storef = find (fun th -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false))(concl th) &&
            can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))(concl th) &&
            (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s23",_))),_)->true|_->false)) asms in
        (* rewrite pshuf1 -> usimd16/TABLE form (pfth). NO WORD_ZX_TRIVIAL (it would wrongly
           collapse the control's double-zx). Use g := the double-zx form to match the store. *)
        let store_full = REWRITE_RULE[pfth] storef in
        let g = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
        let m = `word (val (mask8:int64) MOD 256):byte` in
        let pc = ISPECL [`word_add res (word (4 * outlen0)):int64`; `s23:x86state`; g; m; `LENGTH(ACC_IDX (word (val (mask8:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
        let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
        let spec = ISPECL [g; m; `word_subword (chunk0:int128) (0,8):byte`; `word_subword (chunk0:int128) (8,8):byte`; `word_subword (chunk0:int128) (16,8):byte`; `word_subword (chunk0:int128) (24,8):byte`] SUBITER_STORE_SPEC in
        (* spec's gather hyp (with double-zx g) = bg after collapsing identity word_zx; build gthm. *)
        (let oc=open_out "/tmp/specform.txt" in output_string oc (string_of_term(lhand(concl spec))); close_out oc);
        let gather_hyp = List.nth (conjuncts(lhand(concl spec))) 1 in
        (* gather_hyp = bg modulo word_zx(word_zx ·)=· (identity); EQ_MP the rewrite. *)
        let gthm = EQ_MP (SYM(REWRITE_CONV[WORD_ZX_TRIVIAL] gather_hyp)) bg in
        let specres = MP spec (CONJ mthm gthm) in
        let rej_store = REWRITE_RULE[specres] res_th0 in
        (* ---- SUB-ITER 1 MEMORY FOLD (2026-06-13): fold rej_store (block store at res+4*outlen0)
           with the prefix store into the clean advanced prefix store for SUB_LIST(0,16i+4).
           Done HERE (inner W) so rej_store + mthm are OCaml values in scope (mthm is threaded,
           not assumed, so it can't be re-found). Validated forward inference (/tmp/subiter1_clean.txt).
           Uses LEN_RECONCILE + SUBITER_BLOCK_BYTES + SUBITER_FOLD_STEP + SUB_LIST_SPLIT. ---- *)
        let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
        let blk = `[word_subword (chunk0:int128) (0,8); word_subword chunk0 (8,8); word_subword chunk0 (16,8); word_subword chunk0 (24,8)]:byte list` in
        let prefixbytes = `SUB_LIST(0,16*i) (inlist:byte list)` in
        (* prefix store: read(memory:>bytes(res,4*outlen0)) s23 = nwl(REJ(SUB_LIST(0,16i))).
           identify by: read-eq at s23, RHS has num_of_wordlist+SUB_LIST, address mentions outlen0 (not ACC_IDX). *)
        let prefix_store = find (fun th ->
             (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s23",_))),_) -> true | _ -> false) &&
             hasC "num_of_wordlist" th && hasC "SUB_LIST" th &&
             can(find_term(fun u->u=`res:int64`))(lhand(concl th)) &&
             can(find_term(fun u->u=`outlen0:num`))(lhand(concl th)) &&
             not(hasC "ACC_IDX" th)) asms in
        let len_eq = find (fun th -> match concl th with
             Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asms in
        let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
             (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
        let leninl = find (fun th -> match concl th with
             Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
        let i116 = find (fun th -> match concl th with
             Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
        let lenle = REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1) <= 256 ==> 16*i+16 <= 272`) i116) in
        let lr = MP (ISPECL [m; `chunk0:int128`] LEN_RECONCILE) mthm in
        let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES) (CONJ lenle blk16) in
        let blk_bytes = CONJUNCT1 bb in
        let rej_store2 = REWRITE_RULE[SYM len_eq] rej_store in
        let prefix_store2 = REWRITE_RULE[SYM len_eq] prefix_store in
        let fold = MP (ISPECL [`res:int64`;`s23:x86state`;m;blk;prefixbytes] SUBITER_FOLD_STEP)
                      (CONJ lr (CONJ prefix_store2 rej_store2)) in
        let split0 = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i`;`4`;`0`] SUB_LIST_SPLIT) in
        let clean = REWRITE_RULE[GSYM blk_bytes; GSYM split0] fold in
        (let oc = open_out "/tmp/fold_state.txt" in
         output_string oc ("SUB-ITER 1 FOLD DONE (inner W). clean store =\n"^string_of_term(concl clean)^"\n");
         close_out oc);
        ASSUME_TAC clean))
     THENL
      [(* ---- SUB-ITER 1 fold done (clean advanced prefix store for SUB_LIST(0,16i+4) assumed).
         Marker stop. The counter+mid-guard block (popcnt/add/shr/add s18-21 + cmp/ja s22 ->
         RIP=pc+161, recipe in clean_body_probe.ml stages 1-6) must run BEFORE this store-value
         SUBGOAL_THEN — see ROOT-CAUSE below — so it is NOT placed here. Next step = reorder. *)
       (* ROOT-CAUSE (2026-06-15, main file reloaded + diagnosed): stepping the popcnt (X86_STEPS
          EXEC 18--) AFTER the store-value SUBGOAL_THEN fails "mk_comb: types do not agree".
          R10 s23 = word_zx(word_zx(word(val mask8 MOD 256))) is itself well-typed (byte->i32->i64,
          identical to the probe), and dropping the word_join/usimd16/YMM-read assumptions did NOT
          fix it — so a state read the simulator still needs was left in a broken shape by the
          store-value RULE_ASSUM rewrites. The probe steps counters 18-21 FIRST on the RAW s23
          simulator state, THEN does store-value. FIX (next session): move the counter+mid-guard
          block to right after `X86_STEPS_TAC EXEC (17--17); PURGE_STALE_STATES_TAC ["s16"]`
          (line ~411), BEFORE the `SUBGOAL_THEN !j...gather` block. Counters touch only
          R9/RAX/R8/RCX/flags; the store-value proof reads s23 memory/YMM facts which survive the
          counter steps, so the reorder is sound. The full counter block is preserved verbatim in
          git history (commit prior to this one) and in clean_body_probe.ml stages 1-6. *)
       W(fun (asl,w) ->
         (let oc=open_out "/tmp/integrated_ok.txt" in
          output_string oc (if exists (fun (_,th) -> concl th = `read RIP s23 = word (pc + 167):int64`) asl
                            then "DONE: RIP=pc+167 + store(16i+4)" else "partial");
          close_out oc); NO_TAC)
       ;
       W(fun (asl,w) ->
         let pdef = find (fun th -> is_eq(concl th) && rand(concl th)=`pshuf1:int256` && can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
         let teq = find (fun th -> is_eq(concl th) && lhand(concl th)=`tab1:int256` && can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)) (map snd asl) in
         SUBST1_TAC(SYM pdef) THEN REWRITE_TAC[teq] THEN
         REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
         SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH] THEN
         CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ZX_TRIVIAL; VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV)])
    THENL [ALL_TAC; MASKBIT_PF_TAC])
   THENL
    [ALL_TAC;
     (* bare gather forall proof: JOIN extract over f0sub def *)
     W(fun (asl,w) ->
       let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
       REPEAT STRIP_TAC THEN
       FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
         (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
       REWRITE_TAC[f0d] THEN
       REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
         CONV_TAC NUM_REDUCE_CONV)) THEN
       REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)]) with e -> (let oc=open_out "/tmp/err.txt" in output_string oc ("FAIL: "^Printexc.to_string e^"\n"); close_out oc); REFL `T`);;

Printf.printf "SUBITER1_COMPLETE: prologue->counters->mid-guard(pc+167)->sub-iter-1 store folded (SUB_LIST 0,16i+4). Sub-iters 2-4 pending (see .eta4_instrmap.txt + memory eta4-s22-mkcomb-reorder).\n";;
