(* Sub-iter 2 careful gather (validated 2026-06-17): apply AFTER PREFIX_TAC + acc1 abbrev + VAL_INT64.
   Mirrors sub-iter 1's gather (clean_body_build ~449-466). Key: VERBOSE-step the movzbl + capture,
   else bulk X86_STEPS drops the R10 read and popcnt won't record R9. *)
  X86_VSTEPS_TAC EXEC (24--24) THEN              (* vpsrldq xmm5 (lane shift to nibbles 8-15) *)
  X86_VERBOSE_STEP_TAC EXEC "s25" THEN           (* movzbl %r8b -> r10d *)
  MOVZBL_R10_CAPTURE_TAC THEN
  X86_VSTEPS_TAC EXEC (26--26) THEN REABBREV_TAC `tab2 = read YMM6 s26` THEN   (* vmovq table *)
  X86_VSTEPS_TAC EXEC (27--27) THEN REABBREV_TAC `pshuf2 = read YMM6 s27` THEN (* vpshufb *)
  PURGE_STALE_STATES_TAC ["s26"] THEN
  X86_VSTEPS_TAC EXEC (28--28) THEN REABBREV_TAC `sx2 = read YMM1 s28` THEN    (* vpmovsxbd *)
  (* NEXT: stepA (sx2 = usimd8 (\b.word_sx b)(word_zx(word_zx pshuf2))) via WORD_BLAST;
     then store s29 (X86_STEPS, store-safe via acc1<=248 + VAL); then counter 30-33;
     then sub-iter-2 popeq/bsum/bnd/ja (mask byte = bits 8-15) + resolve mid-guard 2 -> pc+215. *)

(* VALIDATED 2026-06-17 through the STORE: gather (above) + stepA + store all apply cleanly:
   SUBGOAL_THEN `sx2 = usimd8 (\b. word_sx b)(word_zx(word_zx pshuf2))` ASSUME_TAC THENL
    [W(... find sx2 word_join def ...) SUBST1_TAC(SYM sx2def) THEN
     REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_*] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   PURGE_STALE_STATES_TAC ["s27"] THEN
   X86_STEPS_TAC EXEC (29--29)   <- store-safe (acc1<=248 + val(word acc1)=acc1 in scope).
   RESULT: read(memory:>bytes256(res+4*acc1)) s29 = usimd8(\b.word_sx b)(word_zx(word_zx pshuf2)).  GOOD - identical shape to sub-iter 1.

   OPEN: the COUNTER (popcnt s30 / add s31 / shr s32 / add s33) does NOT record `read R9`/`read RAX`
   assumptions (only RCX). So the sub-iter-1 popeq/pop_len fold can't grab R9. This persists even WITH
   the careful gather + MOVZBL_R10_CAPTURE. RCX (add immediate) is recorded; RAX (add %r9d,%eax register
   add) and R9 (popcnt) are NOT. THIS is the real remaining blocker for the mid-guards of sub-iters 2-4.
   Hypothesis to try next: the popcnt R9 value IS in the symbolic state (X86_STEPS just didn't assert it);
   try X86_VERBOSE_STEP for the popcnt+add so the reads are kept, OR grab R9 via the conclusion's
   eventually-state and build popeq against that. Sub-iter 1's R9 read existed at s21 - compare exactly
   how PREFIX's (18--21) differs from this (30--33). *)
