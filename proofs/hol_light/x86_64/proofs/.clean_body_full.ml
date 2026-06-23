(* CLEAN_BODY_FULL_TAC: the complete cheat-free proof of clean_body_tm (the eta4 SIMD loop body,
   pc+56 -> pc+56). Composes the prologue + 4 sub-iter gather/fold/counter/midguard + final state.
   Load order (after main file + cbb_defs):
     .subiter_k_lemmas, .subiter_byte23_lemmas, .maskbit_tgt_tac, .tab1_teq_tac, .pf_target_proof,
     .prefix_g_full_tac, .si1_fold_v2, .maskbit_tgt_2_tac, .tab2_teq_tac, .si2_fold_pieces, .si2_fold_complete,
     .si2_full, .si2_integrated, .si3_full, .si3_fold_pieces, .si3_integrated, .si4_full,
     .si4_fold_pieces, .si4_integrated, .acc_full_len, .rax_final, .rcx_final.
     (.tab2_teq_tac MUST precede .si2_fold_pieces — TAB2_TEQ_TAC dependency. Verified
      reload + reprove cheat-free 2026-06-23, ~153s, hyps=0 = clean_body_tm exactly.) *)
let CLEAN_BODY_FULL_TAC : tactic =
  PREFIX_G_FULL_TAC THEN SI1_FOLD_V2 THEN SI2_INTEGRATED THEN SI3_INTEGRATED THEN SI4_INTEGRATED THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16*i+16 = 16*(i+1)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [RAX_FINAL_TAC; RCX_FINAL_TAC];;
