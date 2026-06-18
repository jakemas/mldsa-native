(* ACC_FULL_LEN: the 5-term niblen sum (outlen0-block + 4 sub-iter blocks) = niblen(SUB_LIST(0,16(i+1))).
   Needed by RAX_FINAL_TAC. Plus SL16_4WAY helper (SUB_LIST(16i,16) = APPEND of the 4 4-blocks). *)
let SL16_4WAY = prove
 (`SUB_LIST(16*i,16) (inlist:byte list) =
   APPEND (SUB_LIST(16*i,4) inlist)
   (APPEND (SUB_LIST(16*i+4,4) inlist)
   (APPEND (SUB_LIST(16*i+8,4) inlist) (SUB_LIST(16*i+12,4) inlist)))`,
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`12`;`16*i`] SUB_LIST_SPLIT) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`8`;`16*i+4`] SUB_LIST_SPLIT) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`4`;`16*i+8`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `(16*i+4)+4=16*i+8`; ARITH_RULE `(16*i+8)+4=16*i+12`;
    ARITH_RULE `4+8=12`; ARITH_RULE `4+4=8`; ARITH_RULE `4+12=16`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let ACC_FULL_LEN = prove
 (`!inlist:byte list. !i:num. 16*i+16 <= LENGTH inlist ==>
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*i) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+4,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+8,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+12,4) inlist):int16 list) =
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(i+1)) inlist):int16 list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `16*(i+1) = 16*i+16`] THEN
  ONCE_REWRITE_TAC[ISPECL[`inlist:byte list`;`16*i`;`16`;`0`] SUB_LIST_SPLIT] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[SL16_4WAY] THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN ARITH_TAC);;
