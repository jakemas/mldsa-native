(* ============================================================================
   Sub-iters 3,4 popcount->length keystones (validated 2026-06-18). Load AFTER
   .subiter_k_lemmas.ml (needs BYTE2_DIVMOD/BYTE3_DIVMOD/divmod_swap/MM* etc.).
   These give POPCNT_BYTE2/BYTE3 = the unweighted lanes-16..23 / 24..31 bitval sums,
   over the double/triple word_ushr mask forms produced by the simulator at sub-iters
   3,4 (mask = R8 after 2 / 3 ushr-by-8). Analogous to POPCNT_BYTE1.
   ============================================================================ *)

(* peel one ushr-8 layer of a 64-bit mask through the i32 round-trip *)
let MASK_USHR8_STEP = prove
 (`!m:int64. val(word_zx(word_ushr(word_zx m:int32) 8):int64) MOD 256 = (val m DIV 256) MOD 256`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[MM64_256; MM32_DIV256]);;

let DIVLT = prove(`!a k e. a < e ==> a DIV k < e`,
  REPEAT STRIP_TAC THEN TRANS_TAC LET_TRANS `a:num` THEN ASM_REWRITE_TAC[DIV_LE]);;

let divmod_swap16 = prove(`!x. (x DIV 2 EXP 16) MOD 2 EXP 8 = (x MOD 2 EXP 24) DIV 2 EXP 16`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;
let divmod_swap24 = prove(`!x. (x DIV 2 EXP 24) MOD 2 EXP 8 = (x MOD 2 EXP 32) DIV 2 EXP 24`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* full val of the byte-1 / byte-2 masks (mask8b = ushr8 once; mask8c = ushr8 twice) *)
let VAL_MASK8B = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64) = (S MOD 4294967296) DIV 256`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `256 = 2 EXP 8`] THEN
  MP_TAC(SPECL[`S:num`;`2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ABBREV_TAC `q = S MOD 2 EXP 32` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 32` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q MOD 2 EXP 64 MOD 2 EXP 32 = q` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN TRANS_TAC LET_TRANS `q:num` THEN REWRITE_TAC[DIV_LE] THEN ASM_REWRITE_TAC[]);;

let VAL_MASK8C = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64) =
       (S MOD 4294967296) DIV 65536`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`] THEN
  MP_TAC(SPECL[`S:num`;`2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ABBREV_TAC `q = S MOD 2 EXP 32` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q < 2 EXP 64 /\ q DIV 2 EXP 8 < 2 EXP 64 /\ q DIV 2 EXP 8 < 2 EXP 32 /\
                q DIV 2 EXP 8 DIV 2 EXP 8 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `q < 2 EXP 64 /\ q < 2 EXP 32` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN TRANS_TAC LTE_TRANS `2 EXP 32` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIVLT]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

(* mask byte for sub-iter 3 (double ushr) = byte 2 ; sub-iter 4 (triple ushr) = byte 3 *)
let MASK_SHIFT16_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64) MOD 256 =
       (S DIV 65536) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_USHR8_STEP; VAL_MASK8B; DIV_DIV] THEN
  REWRITE_TAC[ARITH_RULE `256 * 256 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `65536 = 2 EXP 16`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap16] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let MASK_SHIFT24_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64):int32) 8):int64) MOD 256 =
       (S DIV 16777216) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_USHR8_STEP; VAL_MASK8C; DIV_DIV] THEN
  REWRITE_TAC[ARITH_RULE `65536 * 256 = 16777216`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `16777216 = 2 EXP 24`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap24] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The two popcount keystones, built programmatically from the SUM32 term. *)
let SUMTERM_BYTE23 = `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
   16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
   256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
   4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
   65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
   1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
   16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
   268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31))`;;

let POPCNT_BYTE2 =
  let arg = subst [SUMTERM_BYTE23, `SUMV:num`]
    (subst [`word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word SUMV:int32):int64):int32) 8):int64):int32) 8):int64`, `MASKC:int64`]
       `word_zx(word_zx(word_zx(word(val (MASKC:int64) MOD 256):byte):int32):int64):int32`) in
  prove(mk_forall(`p:num->bool`, mk_eq(mk_comb(`word_popcount:int32->num`, arg),
     `bitval(p 16) + bitval(p 17) + bitval(p 18) + bitval(p 19) +
      bitval(p 20) + bitval(p 21) + bitval(p 22) + bitval(p 23)`)),
    GEN_TAC THEN REWRITE_TAC[MASK_SHIFT16_MOD256; BYTE2_DIVMOD] THEN
    MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
      [16;17;18;19;20;21;22;23] THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let POPCNT_BYTE3 =
  let arg = subst [SUMTERM_BYTE23, `SUMV:num`]
    (subst [`word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word SUMV:int32):int64):int32) 8):int64):int32) 8):int64):int32) 8):int64`, `MASKC:int64`]
       `word_zx(word_zx(word_zx(word(val (MASKC:int64) MOD 256):byte):int32):int64):int32`) in
  prove(mk_forall(`p:num->bool`, mk_eq(mk_comb(`word_popcount:int32->num`, arg),
     `bitval(p 24) + bitval(p 25) + bitval(p 26) + bitval(p 27) +
      bitval(p 28) + bitval(p 29) + bitval(p 30) + bitval(p 31)`)),
    GEN_TAC THEN REWRITE_TAC[MASK_SHIFT24_MOD256; BYTE3_DIVMOD] THEN
    MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
      [24;25;26;27;28;29;30;31] THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

(* cumulative outlen bound through sub-iter 4 (4th block), for the final RAX/store-safety. *)
let SUBITER_OUTLEN_BOUND_4 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 4, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 8, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 12, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `12 + 4 = 16`]
                     (ISPECL [`inlist:byte list`; `12`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 4 = 12`]
                     (ISPECL [`inlist:byte list`; `8`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> DISCH_THEN(fun th3 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th3; th2; th1; REJ_NIBBLES_ETA4_APPEND;
                                LENGTH_APPEND])))) THEN
  ASM_ARITH_TAC);;

Printf.printf "SUBITER_BYTE23_LEMMAS loaded: MASK_USHR8_STEP VAL_MASK8B/8C MASK_SHIFT16/24 POPCNT_BYTE2/3 BOUND_4\n";;
