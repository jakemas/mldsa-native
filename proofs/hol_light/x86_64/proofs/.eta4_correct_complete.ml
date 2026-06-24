(* ========================================================================= *)
(* Self-contained cheat-free proof driver for MLDSA_REJ_UNIFORM_ETA4_CORRECT. *)
(* Runs .reload_all.ml (main file + full CLEAN_BODY chain + scalar-tail +     *)
(* exit-block assets), then proves CORRECT cheat-free. ~15 min total.         *)
(* The resulting theorem MLDSA_REJ_UNIFORM_ETA4_CORRECT_CF has hyps=0.        *)
(* ========================================================================= *)
loadt "/home/ubuntu/mldsa-native/proofs/hol_light/x86_64/proofs/.reload_all.ml";;
loadt "/home/ubuntu/mldsa-native/proofs/hol_light/x86_64/proofs/.midexit_arm.ml";;

let correct_tm =
  `!res buf table (inlist:byte list) pc.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s = num_of_wordlist outlist)
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`;;

let MLDSA_REJ_UNIFORM_ETA4_CORRECT_CF = prove(correct_tm,
  CORRECT_SCAFFOLD_TAC THEN
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THENL
   [OFFSET_ARM_TAC; MIDEXIT_ARM_TAC]);;

Printf.printf "\n=== MLDSA_REJ_UNIFORM_ETA4_CORRECT_CF: hyps=%d (0 = cheat-free) ===\n"
  (List.length (hyp MLDSA_REJ_UNIFORM_ETA4_CORRECT_CF));;
