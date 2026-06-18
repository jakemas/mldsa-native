(* ===== pf_target proof for sub-iter 1 (GENUINE table-load bridge, no cheat) =====
   Establishes pshuf1 = pf_target by: SYM pshuf1-word_join def, rewrite tab1 via the
   genuine teq (tab1 = word_zx^k(word(nwl(TABLE_ENTRY(word(val mask8 MOD 256)))))) derived
   by TAB1_TEQ_TAC, expand usimd16, then COLLAPSE the redundant word_zx towers:
     - SUBWORD_ZX_LOW: word_subword(word_zx y)(lo,wid) = word_subword y (lo,wid) when lo+wid<=dimindex(P)
       (covers BOTH widening and narrowing zx, since only the low target bits matter)
     - ZX_128_256_128: word_zx(word_zx(x:int128):int256):int128 = x   (the f0sub gather-source g) *)
let SUBWORD_ZX_LOW = prove
 (`!(y:(M)word) lo wid. lo + wid <= dimindex(:P)
     ==> word_subword (word_zx y:(P)word) (lo,wid):(N)word = word_subword y (lo,wid)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_ZX] THEN
  ASM_CASES_TAC `k < MIN wid (dimindex(:N))` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ARITH_RULE `k < MIN a b <=> k < a /\ k < b`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lo + k < dimindex(:P)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let ZX_128_256_128 = prove(`!(x:(128)word). word_zx(word_zx x:(256)word):(128)word = x`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_128] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_ZX; DIMINDEX_128; DIMINDEX_256] THEN
  SUBGOAL_THEN `k < 128 /\ k < 256` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let SUBWORD_ZX_LOW_CONV : conv =
  fun tm ->
      let inst = PART_MATCH (lhs o snd o dest_imp) SUBWORD_ZX_LOW tm in
      let ant = REWRITE_RULE[DIMINDEX_4;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] inst in
      MP ant (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl ant))));;

(* PF_PROOF : tactic — discharges the `pshuf1 = pf_target` SUBGOAL at s23 *)
let PF_PROOF : tactic =
  W(fun (asl,w) ->
    let pdef = find (fun th -> is_eq(concl th) && rand(concl th)=`pshuf1:int256` && can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
    let teq0 = find (fun th -> is_eq(concl th) &&
        (lhand(concl th)=`tab1:int256` || rand(concl th)=`tab1:int256`) &&
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th) &&
        not(can(find_term(fun u->u=`f1bnd:int256`))(concl th))) (map snd asl) in
    let teq = if lhand(concl teq0)=`tab1:int256` then teq0 else SYM teq0 in
    SUBST1_TAC(SYM pdef) THEN REWRITE_TAC[teq] THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ZX_TRIVIAL; VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV SUBWORD_ZX_LOW_CONV) THEN REWRITE_TAC[ZX_128_256_128]);;

(* SUBWORD_USHR: word_subword(word_ushr x n)(lo,wid) = word_subword x (lo+n,wid). Needed for
   the >>64-shifted gather sources of sub-iters 2 and 4 (vpsrldq). *)
let SUBWORD_USHR = prove
 (`!(x:(M)word) n lo wid. word_subword (word_ushr x n) (lo,wid):(N)word = word_subword x (lo+n,wid)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_USHR] THEN
  REWRITE_TAC[ARITH_RULE `(lo + k) + n = (lo + n) + k`]);;
