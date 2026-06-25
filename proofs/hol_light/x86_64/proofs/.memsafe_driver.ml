(* Self-contained MEMSAFE driver: reload eta4 + set up clean_body_ms_tm + test PREFIX_G_FULL_MS.
   Logs progress to /tmp/memsafe_drv.log. Run after a fresh session. *)
let dlog s = let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/memsafe_drv.log" in
              output_string oc (s ^ "\n"); close_out oc;;
(let oc = open_out "/tmp/memsafe_drv.log" in output_string oc "DRV START\n"; close_out oc);;
let contains sub s = let n=String.length sub and m=String.length s in
  let rec go i = i+n<=m && (String.sub s i n = sub || go (i+1)) in go 0;;
Sys.chdir "/home/ubuntu/mldsa-native/proofs/hol_light";;
loaded_files := List.filter (fun (s,_) -> not (contains "rej_uniform_eta4" s)) (!loaded_files);;

let pdir = "/home/ubuntu/mldsa-native/proofs/hol_light/x86_64/proofs/";;
loadt (pdir ^ "rej_uniform_eta4_avx2_asm.ml");;
dlog "main file loaded";;
needs "s2n_bignum/x86/proofs/consttime.ml";;
dlog "consttime loaded";;
loadt "/home/ubuntu/hol-light/s2n-bignum/common/consttime.ml";;
dlog "fork consttime loaded";;

(* allowed_vars_e + EXISTS_E2_TAC *)
let allowed_vars_e : term list ref = ref [];;
let NIL_IMPLIES_APPEND_EQ =
  prove(`!(l:(A)list) m m'. m = m' /\ [] = l ==> m = APPEND l m'`, MESON_TAC[APPEND]);;
let EXISTS_E2_TAC allowed_vars_e =
  (MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL [
    REFL_TAC; SAFE_UNIFY_REFL_TAC allowed_vars_e (ref ["f_events_callee"]) ]) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
   TRY (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e (ref ["f_events_callee"]));;
dlog "EXISTS_E2_TAC defined";;

(* memsafe helpers (DISCHARGE_MEMSAFE_TAC etc.) *)
loadt (pdir ^ "tmp_memsafe_helpers.ml");;
(* keepev stepping *)
let X86_SINGLE_STEP_KEEPEV_TAC th s =
  time (X86_VERBOSE_STEP_TAC th s) THEN DISCARD_OLDSTATE_KEEP_EVENTS_TAC s THEN CLARIFY_TAC;;
let X86_STEPS_KEEPEV_TAC th snums =
  MAP_EVERY (X86_SINGLE_STEP_KEEPEV_TAC th) (statenames "s" snums);;
dlog "keepev stepping defined";;

(* MEMSAFE_LOOPINV + clean_body_ms_tm *)
let MEMSAFE_LOOPINV =
 `\i s.
      read RSP s = stackpointer /\
      read (memory :> bytes (buf,272)) s = num_of_wordlist inlist /\
      read (memory :> bytes (table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
      read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
      read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist))) /\
      read RCX s = word(16*i) /\
      read(memory :> bytes(res,4*LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist)))) s =
        num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist)) /\
      (exists e_acc.
         read events s = APPEND e_acc e /\
         memaccess_inbounds e_acc [buf,272; table,2048] [res,1024])`;;

let clean_body_ms_tm =
  let qvars, body = strip_forall (concl MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;
dlog "clean_body_ms_tm built";;

(* _MS body tactics (these embed MEMSAFE_COND_CLEANUP_TAC) *)
loadt (pdir ^ ".prefix_g_full_tac_ms.ml");;
loadt (pdir ^ ".si2_integrated_ms.ml");;
loadt (pdir ^ ".si3_integrated_ms.ml");;
loadt (pdir ^ ".si4_integrated_ms.ml");;
dlog "MS tactics loaded";;

(* TEST: PREFIX_G_FULL_MS_TAC on clean_body_ms_tm *)
(let r =
   (try let _ = prove(clean_body_ms_tm,
          PREFIX_G_FULL_MS_TAC THEN SI1_FOLD_V2 THEN SI2_INTEGRATED_MS THEN SI3_INTEGRATED_MS THEN SI4_INTEGRATED_MS THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16*i+16 = 16*(i+1)`]) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [RAX_FINAL_TAC; CONJ_TAC THENL [RCX_FINAL_TAC; ALL_TAC]]) in
        "FULL BODY proved (incl RAX/RCX); events conjunct left"
    with Failure m -> "FAIL: "^m | e -> "EXN: "^Printexc.to_string e) in
 dlog ("RESULT: "^r));;
dlog "DRV DONE";;
