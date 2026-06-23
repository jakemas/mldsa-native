(* ========================================================================= *)
(* SCALAR_TAIL_RUN: byte-loop-to-exit by strong induction on byte-budget d.   *)
(* Needs hyp LENGTH(REJ(SUB(0,p)))<=256 (the SIMD loop exits with outlen<=256, *)
(* so count-exit gives outlen=256 exactly = cap length). Load after main +     *)
(* .scalar_tail_lemmas + .scalar_tail_build + .scalar_body_lemma.              *)
(*                                                                            *)
(* STATUS: base case (p=272) VALIDATED interactively end-to-end. Count-exit    *)
(* stepping confirmed: JAE_TAKEN_GE fact on RAX -> X86_VSTEPS(1--2) resolves    *)
(* cmp eax,256 jae TAKEN -> pc+406. Inductive step (clean recursive via         *)
(* SCALAR_TAIL_BODY + ENSURES_TRANS with IH, mid-byte terminal) under          *)
(* construction. See eta4-scalar-tail-progress.md for the validated tactics.   *)
(* ========================================================================= *)

let SCALAR_TAIL_RUN = prove
 (`!d res buf table (inlist:byte list) pc (p:num) stackpointer.
        272 - p <= d /\
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        p <= 272 /\
        LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 256
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 318) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)) /\
                  read RCX s = word p /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list))) s =
                    num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)))
             (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                   read RAX s = word(LENGTH outlist) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  CHEAT_TAC);;
