(* Master reload after session wipe (reauth). Loads main eta4 file + clean_body_build
   helpers + full CLEAN_BODY chain, then PROVES CLEAN_BODY + CLEAN_BLOCK, then scalar
   tail + bridge lemmas + scaffold. Logs per-step status to /tmp/reload_log.txt since
   loadt swallows tail errors. *)

let _logf = "/tmp/reload_log.txt";;
let logmsg s = let oc = open_out_gen [Open_append;Open_creat] 0o644 _logf in
               output_string oc (s ^ "\n"); close_out oc;;
(let oc = open_out _logf in output_string oc "RELOAD START\n"; close_out oc);;

let contains sub s = let n=String.length sub and m=String.length s in
  let rec go i = i+n<=m && (String.sub s i n = sub || go (i+1)) in go 0;;

Sys.chdir "/home/ubuntu/mldsa-native/proofs/hol_light";;
logmsg ("cwd=" ^ Sys.getcwd());;
logmsg ("o_exists=" ^ string_of_bool (Sys.file_exists "x86_64/mldsa/rej_uniform_eta4_avx2_asm.o"));;
loaded_files := List.filter (fun (s,_) -> not (contains "rej_uniform_eta4" s)) (!loaded_files);;

let pdir = "/home/ubuntu/mldsa-native/proofs/hol_light/x86_64/proofs/";;
let step name f =
  (try f (); logmsg ("OK   " ^ name)
   with e -> logmsg ("FAIL " ^ name ^ " : " ^ Printexc.to_string e); raise e);;
let L f = step f (fun () -> loadt (pdir ^ f));;

(* 1. main file (~440s) *)
L "rej_uniform_eta4_avx2_asm.ml";;

(* 2. clean_body_build: clean_body_tm + EXEC + CBB helpers + CBB_SI1_TAC *)
L "clean_body_build.ml";;

(* 3. CLEAN_BODY chain (order per .clean_body_full.ml header) *)
L ".subiter_k_lemmas.ml";;
L ".subiter_byte23_lemmas.ml";;
L ".maskbit_tgt_tac.ml";;
L ".tab1_teq_tac.ml";;
L ".pf_target_proof.ml";;
L ".prefix_g_full_tac.ml";;
L ".si1_fold_v2.ml";;
L ".maskbit_tgt_2_tac.ml";;
L ".tab2_teq_tac.ml";;
L ".si2_fold_pieces.ml";;
L ".si2_fold_complete.ml";;
L ".si2_full.ml";;
L ".si2_integrated.ml";;
L ".si3_full.ml";;
L ".si3_fold_pieces.ml";;
L ".si3_integrated.ml";;
L ".si4_full.ml";;
L ".si4_fold_pieces.ml";;
L ".si4_integrated.ml";;
L ".acc_full_len.ml";;
L ".rax_final.ml";;
L ".rcx_final.ml";;
L ".clean_body_full.ml";;

(* 4. Prove CLEAN_BODY (~153s) under the canonical name the scaffold expects, then CLEAN_BLOCK *)
let MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY = prove(clean_body_tm, CLEAN_BODY_FULL_TAC);;
logmsg ("OK   PROVE CLEAN_BODY hyps=" ^ string_of_int (List.length (hyp MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY)));;
L ".clean_block.ml";;

(* 5. scalar tail chain *)
L ".scalar_tail_lemmas.ml";;
L ".scalar_tail_build.ml";;
L ".scalar_body_lemma.ml";;
L ".scalar_tail_run.ml";;

(* 6. bridge lemmas + scaffold *)
L ".subiter_bridge_lemmas.ml";;
L ".correct_scaffold.ml";;

(* 7. exit-block assets *)
L ".exit_offset.ml";;        (* EXIT_OFFSET (cheat-free, offset arm) *)
L ".exit_block.ml";;         (* OFFSET_ARM_TAC + EXIT_OFFSET_NOLET *)
L ".midexit_prefix.ml";;     (* PREFIX_TO_S21_TAC *)
L ".mg1_nt.ml";;             (* MG1_NT_TAC *)
L ".mg2_nt.ml";;             (* MG2_NT_TAC *)
L ".mg3_nt.ml";;             (* MG3_NT_TAC *)
L ".si4_body4.ml";;          (* SI4_BODY4_TAC *)
L ".midexit_subiter1.ml";;   (* MID_EXIT_SUBITER1 + RCX4_COLLAPSE (mid-exit case-1) *)
L ".midexit_subiter2.ml";;   (* MID_EXIT_SUBITER2 + SI2_BODY_TAC + SI2_MG2_TAKEN_TAC (case-2) *)
L ".midexit_subiter3.ml";;   (* MID_EXIT_SUBITER3 + SI3_BODY3_TAC + SI3_MG3_TAKEN_TAC (case-3) *)
L ".midexit_case4.ml";;      (* MID_EXIT_CASE4 (case-4) *)

logmsg "RELOAD COMPLETE";;
