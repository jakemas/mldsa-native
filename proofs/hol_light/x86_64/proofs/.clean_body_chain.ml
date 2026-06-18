(* ============================================================================
   CLEAN_BODY assembled chain (2026-06-18). Loads the full validated tactic chain
   that proves MLDSA_REJ_UNIFORM_ETA4 clean_body_tm DOWN TO a single remaining
   subgoal: the store-value recombination.

   Prerequisites (loadt in order, after main file + clean_body_build.ml helpers):
     .subiter_k_lemmas.ml        (POPCNT_BYTE1, zxbyte_eq, BYTE1/2/3_DIVMOD, ...)
     .subiter_byte23_lemmas.ml   (POPCNT_BYTE2/3, MASK_SHIFT16/24, SUBITER_OUTLEN_BOUND_4, ...)
     .prefix4_tac.ml             (PREFIX4_TAC)
     .si2_full.ml .si3_full.ml .si4_full.ml
     .rax_final.ml .rcx_final.ml (+ ACC_FULL_LEN, RCX helpers — defined within)

   The chain:
     PREFIX4_TAC THEN SI2_GATHER THEN SI2_MG_TAC THEN SI2_RESOLVE THEN
     SI3_PRE THEN SI3_GATHER THEN SI3_MG THEN SI3_RESOLVE THEN
     SI4_PRE THEN SI4_GATHER THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL [ RAX_FINAL_TAC; RCX_FINAL_TAC; ALL_TAC ]
   reaches RIP s57 = pc+56 and discharges all final-state conjuncts EXCEPT:

     read (memory :> bytes(res, 4*LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist)))) s57
       = num_of_wordlist (REJ_SAMPLE_ETA4_BYTES (SUB_LIST(0,16*(i+1)) inlist))

   REMAINING: the store recombination. The 4 sub-iter store-read facts are lost by
   s57 (each is keyed to an intermediate state s17/s29/s41 and dropped by
   PURGE_STALE_STATES + stepping; only the initial prefix store at res and
   sub-iter 4's bytes256(res+4*acc3)=sx4 survive). FIX: fold each store into the
   running prefix IMMEDIATELY after its X86_STEPS (clean_body_build.ml sub-iter-1
   recipe: SUBITER_STORE_SPEC (store value = REJ_SAMPLE of block bytes, given the
   maskbit forall + the per-sub-iter gather forall word_subword(lane-window)(8j,8)
   = word_sub 4 nibble) + SUBITER_STORE_POSTCOND + SUBITER_FOLD_STEP), producing
   read(bytes(res,4*acc_k)) = nwl(REJ(SUB_LIST(0,16i+4k))). Restructure SI*_GATHER
   to insert this fold after the store step (s17 for si1 — done in PREFIX tail's
   marker-stopped block; s29/s41/s53 for si2/3/4). The per-sub-iter gather forall
   uses the f0sub lane window matching the vextracti128/vpsrldq lane: si1=lane0 low,
   si2=lane0 hi-via-vpsrldq, si3=lane1 (vextracti128 ,1), si4=lane1 hi-via-vpsrldq.
   ============================================================================ *)

Printf.printf "CLEAN_BODY_CHAIN: documentation only; see the chain comment. Run the chain interactively.\n";;
