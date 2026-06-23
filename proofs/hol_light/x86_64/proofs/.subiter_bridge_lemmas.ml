(* ========================================================================= *)
(* Sub-iteration spec bridges for the Phase-2 SIMD-loop RE-DECOMPOSITION.      *)
(* eta4's SIMD loop has per-sub-iteration `cmp eax,248; ja scalar` mid-guards  *)
(* (file offsets 0xa0/0xd8/0x10d; the head 0x3c also has cmp ecx,256). To get  *)
(* the TIGHT outlen0<=256 bound at scalar-tail entry (which the 16-byte-block  *)
(* invariant only bounds <=280), the loop must be counted at 4-byte sub-iter   *)
(* granularity. These mirror PR1014's SIMD_ITERATION_BRIDGE (8 elems/iter,      *)
(* adds <=8) + its outlen<=256 derivation (PR1014 lines 3734-3759).            *)
(* Load after the main eta4 file. *)
(* ========================================================================= *)

(* A 4-byte sub-iteration contributes <= 8 output coefficients. *)
let SUBITER_STEP_BOUND_8 = prove
 (`!(inlist:byte list) k.
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(k,4) inlist):int32 list) <= 8`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(k,4) (inlist:byte list)` LENGTH_REJ_SAMPLE_ETA4_BYTES_BOUND) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* Processing 4 more input bytes appends their samples; length grows by <= 8. *)
let SUBITER_BRIDGE_ETA4 = prove
 (`!(inlist:byte list) p.
     p + 4 <= LENGTH inlist
     ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+4) inlist):int32 list =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(p,4) inlist)) /\
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+4) inlist):int32 list) =
           LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) +
           LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(p,4) inlist):int32 list) /\
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(p,4) inlist):int32 list) <= 8`,
  REPEAT STRIP_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `p + 4 = 0 + (p + 4)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`;`p:num`;`4`;`0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND];
    ONCE_REWRITE_TAC[ARITH_RULE `p + 4 = 0 + (p + 4)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`;`p:num`;`4`;`0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND; LENGTH_APPEND];
    REWRITE_TAC[SUBITER_STEP_BOUND_8]]);;

(* The TIGHT bound: count <=248 before the last sub-iter guard => <=256 after  *)
(* processing the 4 bytes. This discharges SCALAR_TAIL_FROM_RUN's              *)
(* `LENGTH(REJ(SUB(0,16N)))<=256` hypothesis from the sub-iter loop invariant. *)
let OUTLEN0_LE_256_FROM_SUBITER = prove
 (`!(inlist:byte list) p.
     p + 4 <= LENGTH inlist /\
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+4) inlist):int32 list) <= 256`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inlist:byte list`;`p:num`] SUBITER_BRIDGE_ETA4) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in
    can (find_term (fun t -> t = `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(p,4) inlist):int32 list`)) c
    || c = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 248`))) THEN
  ARITH_TAC);;
