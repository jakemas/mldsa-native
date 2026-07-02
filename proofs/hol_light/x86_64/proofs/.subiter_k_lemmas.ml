(* ============================================================================
   Sub-iter k (k>=1) popcount->length keystone lemmas, validated 2026-06-17.
   These generalize sub-iter 1's popeq/pop_len recipe to sub-iters 2,3,4 whose
   mask byte is R8 shifted right by 8*k bits.  Load AFTER the main file +
   clean_body_build.ml helpers.

   THE UNBLOCK (see memory eta4-subiter2-r9-unblocked): right after PREFIX_TAC
   reaches clean s23 (RIP=pc+163), REABBREV_TAC `mask8b = read R8 s23` to a BARE
   var BEFORE the sub-iter-2 movzbl.  Then after the movzbl + MOVZBL_R10_CAPTURE,
   fold read R8 s24 = mask8b, giving the clean R10 shape
   word_zx(word_zx(word(val mask8b MOD 256))) -- identical to sub-iter 1.  The
   popcnt at s30 then records `read R9 s30 = word_zx(word(word_popcount(
   word_zx(word_zx(word_zx(word(val mask8b MOD 256))))))) ` -- clean.  The memory's
   prior "no R9 assertion, mlkem rebuild required" conclusion was WRONG; it was a
   missing REABBREV, not a wall.
   ============================================================================ *)

(* a MOD 2^64 MOD 256 = a MOD 256 *)
let MM64_256 = prove
 (`!a. a MOD 18446744073709551616 MOD 256 = a MOD 256`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
    [ARITH_RULE `18446744073709551616 = 256 * 72057594037927936`] THEN
  REWRITE_TAC[MOD_MOD]);;

(* a MOD 2^32 MOD 2^64 = a MOD 2^32 *)
let MM32_64 = prove
 (`!a. a MOD 4294967296 MOD 18446744073709551616 = a MOD 4294967296`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL[`a:num`;`4294967296`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* (x DIV 2^8) MOD 2^8 = (x MOD 2^16) DIV 2^8 *)
let divmod_swap = prove
 (`!x. (x DIV 2 EXP 8) MOD 2 EXP 8 = (x MOD 2 EXP 16) DIV 2 EXP 8`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* (S MOD 2^32 DIV 256) MOD 256 = (S DIV 256) MOD 256 *)
let MM32_DIV256 = prove
 (`!S. (S MOD 4294967296 DIV 256) MOD 256 = (S DIV 256) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* mask8b = word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64,
   the R8-shifted-by-8 value at the start of sub-iter 2.  Its low byte = byte 1 of S. *)
let MASK_SHIFT8_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64) MOD 256 =
       (S DIV 256) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[MM32_64; MOD_MOD_REFL; MM64_256; MM32_DIV256]);;

(* byte 1 of the 32-lane VPMOVMSKB bitval sum = the lanes-8..15 weighted sum.
   Composes MASK_SHIFT8_MOD256: after the ushr, (val mask8b MOD 256) = (SUM32 DIV 256) MOD 256
   = this, the byte-1 positional sum. *)
let BYTE1_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 256) MOD 256 =
    bitval(p 8) + 2*bitval(p 9) + 4*bitval(p 10) + 8*bitval(p 11) +
    16*bitval(p 12) + 32*bitval(p 13) + 64*bitval(p 14) + 128*bitval(p 15)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)) +
    256 * (bitval(p 8) + 2*bitval(p 9) + 4*bitval(p 10) + 8*bitval(p 11) +
     16*bitval(p 12) + 32*bitval(p 13) + 64*bitval(p 14) + 128*bitval(p 15) +
     256*(bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
     16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23) +
     256*(bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31))))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW8_LT; DIV_LT; ADD_CLAUSES] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE
   `bitval (p 8) + 2 * bitval (p 9) + 4 * bitval (p 10) + 8 * bitval (p 11) +
    16 * bitval (p 12) + 32 * bitval (p 13) + 64 * bitval (p 14) + 128 * bitval (p 15) + Z =
    (bitval (p 8) + 2 * bitval (p 9) + 4 * bitval (p 10) + 8 * bitval (p 11) +
     16 * bitval (p 12) + 32 * bitval (p 13) + 64 * bitval (p 14) + 128 * bitval (p 15)) + Z`] THEN
  MATCH_MP_TAC ADD256_MOD THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [8;9;10;11;12;13;14;15] THEN ARITH_TAC);;

(* SUB-ITER 2 popcount = unweighted lanes-8..15 bitval sum.  This is the sub-iter-2
   analog of POPCNT_VPMOVMSKB_LOW8 (which handles sub-iter 1's lanes 0..7).  After the
   mask8b fold the R9 popcount at s30 matches this LHS with
   p k := bit 7 (word_subword f1bnd (8*k,8)).  Compose with the wide maskbit fact
   (bit 7 (f1bnd byte k) <=> val(nibble k) < 9, provable for all 32 lanes via MASK_WIDE)
   to get the lanes-8..15 sum = LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+4,4) inlist)). *)
let POPCNT_BYTE1 = prove
 (`!p:num->bool.
     word_popcount
       (word_zx (word_zx (word_zx
          (word (val (word_zx (word_ushr (word_zx (word_zx
             (word (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
              16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
              256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
              4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
              65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
              1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
              16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
              268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)):int32):int64):int32) 8):int64)
            MOD 256):int32):int32):int32):int32) =
     bitval(p 8) + bitval(p 9) + bitval(p 10) + bitval(p 11) +
     bitval(p 12) + bitval(p 13) + bitval(p 14) + bitval(p 15)`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_SHIFT8_MOD256; BYTE1_DIVMOD] THEN
  MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
    [8;9;10;11;12;13;14;15] THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* zxbyte_eq: the simulator's R9 popcount arg has zx types byte->i32->i64->i32, while
   POPCNT_BYTE1 was stated all-i32 (HOL's default).  They print identically but aconv=false.
   This bridges them for v<256 (both = word v:int32).  Use:
   TRANS (AP_TERM `word_popcount` (MP (SPEC `val mask8b MOD 256` zxbyte_eq) <v<256>)) pop_len2
   gives pop_len2 over the simulator's exact type, so REWRITE fires on the mid-guard COND. *)
let zxbyte_eq = prove
 (`!v. v < 256 ==>
     word_zx(word_zx(word_zx(word v:byte):int32):int64):int32 =
     word_zx(word_zx(word_zx(word v:int32):int32):int32):int32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 256 ==> v < 2 EXP 8 /\ v < 2 EXP 32 /\ v < 2 EXP 64`] THEN
  CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 256 ==> v < 2 EXP 8 /\ v < 2 EXP 32`]);;

(* TODO sub-iters 3,4: BYTE2_DIVMOD / BYTE3_DIVMOD ((SUM32 DIV 65536) MOD 256 etc.) +
   MASK_SHIFT16/24_MOD256 (double/triple word_ushr by 8) + POPCNT_BYTE2/BYTE3.  Same
   shape as BYTE1; the SUBST1_TAC reassociation peels one more 256* factor each. *)


let LOW16_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) < 65536`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15] THEN ARITH_TAC);;
let LOW24_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) < 16777216`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23] THEN ARITH_TAC);;

(* BYTE2_DIVMOD: (SUM32 DIV 65536) MOD 256 = lanes-16..23 weighted sum.
   BYTE3_DIVMOD: (SUM32 DIV 16777216) MOD 256 = lanes-24..31 weighted sum (top byte, no MOD needed
   but we keep MOD 256 form for uniformity). *)
let BYTE2_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 65536) MOD 256 =
    bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
    16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15)) +
    65536 * ((bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
     16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23)) +
     256*(bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31)))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW16_LT; DIV_LT; ADD_CLAUSES] THEN
  MATCH_MP_TAC ADD256_MOD THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [16;17;18;19;20;21;22;23] THEN ARITH_TAC);;

let BYTE3_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 16777216) MOD 256 =
    bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
    16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23)) +
    16777216 * (bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW24_LT; DIV_LT; ADD_CLAUSES] THEN
  MATCH_MP_TAC MOD_LT THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [24;25;26;27;28;29;30;31] THEN ARITH_TAC);;

Printf.printf "SUBITER_K_LEMMAS loaded\n";;
