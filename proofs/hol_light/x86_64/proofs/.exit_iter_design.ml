(* Correct decomposition of MLDSA_REJ_UNIFORM_ETA4_CORRECT's SIMD loop, given the production
   binary has MID-ITERATION guards (cmpl $248,ctr; ja scalar after sub-iters 1/2/3).
   The 16-byte ENSURES_WHILE_UP2 framing with body_tm (RCX=16(i+1)) is WRONG for the last
   iteration (a mid-guard can fire -> exit at pc+318 with pos=16i+4k, partial ctr).

   DESIGN: run the outer loop for N-1 CLEAN iterations (no mid-guard fires, since for i+1<N
   niblen(16(i+1))<=248 => all intermediate sub-iter outlens <=248 by INTERMED_OUTLEN_LE =>
   CLEAN_BODY applies), then handle iteration i=N-1 as a SEPARATE straight-line segment that
   case-splits on which guard (top, or after sub-iter 1/2/3, or sub-iter 4 -> top of next) fires
   and exits to pc+318. The per-sub-iter gather/fold tactics (SI1_FOLD_V2, SI2/3/4_INTEGRATED)
   are reusable for the last-iteration sub-iters; the new work is the guard-TAKEN branches. *)

(* INTERMED_OUTLEN_LE: for clean iterations, intermediate sub-iter outlens stay <=248 (no mid-exit).
   niblen monotone in prefix length: niblen(16i+k) <= niblen(16i+16) <= 248. *)
let INTERMED_OUTLEN_LE = prove
 (`!inlist:byte list. !i k.
     k <= 16 /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*i+16) inlist):int16 list) <= 248
     ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*i+k) inlist):int16 list) <= 248`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LE_TRANS `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*i+16) inlist):int16 list)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ASM_ARITH_TAC);;
