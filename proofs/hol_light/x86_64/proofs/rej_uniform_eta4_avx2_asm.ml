(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Rejection uniform sampling for eta=4 (x86_64 AVX2).                *)
(* ========================================================================= *)

(* Ensure namespaced imports (s2n_bignum/, mldsa_native/) resolve.           *)
(* The Nix shellHook sets IMPORTS_DIR to <PROOF_DIR>/.imports and creates    *)
(* symlinks s2n_bignum -> $S2N_BIGNUM_DIR and mldsa_native -> $PROOF_DIR.    *)
(* Outside Nix (e.g. MCP/checkpoint runtime), IMPORTS_DIR may be unset, so   *)
(* prepend the conventional path to load_path explicitly.                    *)
let () =
  let imports = "/home/ubuntu/mldsa-native/proofs/hol_light/.imports" in
  if Sys.file_exists imports && not (List.mem imports !load_path) then
    load_path := imports :: !load_path;;

needs "s2n_bignum/x86/proofs/base.ml";;
needs "mldsa_native/common/mldsa_specs.ml";;
needs "mldsa_native/x86_64/proofs/mldsa_utils.ml";;
needs "mldsa_native/x86_64/proofs/mldsa_rej_uniform_table.ml";;

(* Reject silent type-variable invention.                                    *)
(* Without this, polymorphic patterns (e.g. TAUT, MESON) can invent fresh   *)
(* type variables that mismatch across subgoals, leading to                 *)
(* "seqapply: Length mismatch" errors that don't reproduce interactively.   *)
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Debugging tactics — print/dump the current goal state without changing  *)
(* anything. Useful during proof development; harmless to leave in.         *)
(* ------------------------------------------------------------------------- *)

(* PRINT_GOAL_TAC — prints the current goal then no-op. *)
let PRINT_GOAL_TAC = fun g ->
  let (_, goal) = g in
  Printf.printf "==== GOAL ====\n%s\n==============\n%!" (string_of_term goal);
  ALL_TAC g;;

(* DUMP_STATE_TAC — writes goal + all hyps to a file. Best-effort: silently
   no-op if the directory does not exist (e.g. in CI), so safe to leave in. *)
let DUMP_STATE_TAC path = fun g ->
  let (hyps, goal) = g in
  (try
    let oc = open_out path in
    output_string oc (Printf.sprintf "=== GOAL ===\n%s\n\n=== HYPS (%d) ===\n"
      (string_of_term goal) (List.length hyps));
    List.iter (fun (name, th) ->
      output_string oc (Printf.sprintf "[%s]: %s\n\n" name
        (string_of_term (concl th)))) hyps;
    close_out oc
  with _ -> ());
  ALL_TAC g;;

(* DBG — prints a tracer message then no-op. Switch to `let DBG _ = ALL_TAC`*)
(* for silent production builds.                                            *)
let DBG s:tactic = fun g -> Printf.printf "DBG: %s\n%!" s; ALL_TAC g;;

(* ------------------------------------------------------------------------- *)
(* Simulator compatibility shim: extend REGISTER_ALIASES with r8b..r15b and  *)
(* r8w..r15w so OPERAND_SIZE_CONV reduces register_size for REX-extended     *)
(* byte/word registers used by the eta4/eta2 asm (movzbl r10d, r8b etc.).   *)
(* This rebuilds the X86_CONV / X86_BASIC_STEP_TAC / X86_STEPS_TAC chain    *)
(* with the new aliases.                                                    *)
(* ------------------------------------------------------------------------- *)

let REGISTER_ALIASES =
 [rax;  rcx;  rdx;  rbx;  rsp;  rbp;  rsi;  rdi;
  r8;   r9;  r10;  r11;  r12;  r13;  r14;  r15;
  eax; ecx; edx; ebx; esp; ebp; esi; edi;
  r8d; r9d; r10d; r11d; r12d; r13d; r14d; r15d;
  ax; cx; dx; bx; sp; bp; si; di; ah;
  r8w; r9w; r10w; r11w; r12w; r13w; r14w; r15w;
  al; ch; cl; dh; dl; bh; bl; spl; bpl; sil; dil;
  r8b; r9b; r10b; r11b; r12b; r13b; r14b; r15b;
  xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7;
  xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15;
  ymm0; ymm1; ymm2; ymm3; ymm4; ymm5; ymm6; ymm7;
  ymm8; ymm9; ymm10; ymm11;ymm12; ymm13; ymm14; ymm15];;

let OPERAND_SIZE_CONV =
  let topconv = GEN_REWRITE_CONV I [operand_size]
  and botconv = GEN_REWRITE_CONV TOP_DEPTH_CONV (QWORD::REGISTER_ALIASES)
  and midconv = GEN_REWRITE_CONV REPEATC
   [simdregister_size; register_size; bytesize; simdregsize; regsize] in
  fun tm ->
    match tm with
      Comb(Const("operand_size",_),_)->
          (botconv THENC topconv THENC midconv) tm
    | _ -> failwith "OPERAND_SIZE_CONV";;

let X86_CONV (decode_ths:thm option array) ths tm =
  let pc_th = try find
    (fun th ->
      let c = concl th in
      is_eq c && is_read_rip (fst (dest_eq c)))
    ths with _ ->
      failwith "X86_CONV: can't find `read RIP .. = ..` from ths" in
  let bytes_loaded_mc_ths:thm list =
    let the_mc:term option = Option.bind decode_ths.(0)
      (fun th ->
        let t = concl th in
        let bytes_loaded_term = fst (dest_imp (snd (strip_forall t))) in
        let the_mc = last (snd (strip_comb bytes_loaded_term)) in
        if is_const the_mc then Some the_mc else None) in
    let bytes_loaded_tm = `bytes_loaded` in
    let res = filter (fun th ->
        let cc = concl th in is_comb cc && (
        let c,args = strip_comb (concl th) in
        c = bytes_loaded_tm &&
          (the_mc = None || last args = Option.get the_mc)))
      ths in
    if res = [] then failwith
        ("X86_CONV: can't find `bytes_loaded .. .. " ^
          (if the_mc <> None then string_of_term (Option.get the_mc) else "..")
          ^ "` from ths")
    else res in
  let eth = tryfind (fun loaded_mc_th ->
      GEN_REWRITE_CONV I [X86_THM decode_ths loaded_mc_th pc_th] tm)
    bytes_loaded_mc_ths in
  let x86_execute_case_rules:thm list =
    let ts = find_terms is_const (concl eth) in
    List.filter_map (fun t ->
      try Some ((assoc (name_of t) X86_EXECUTE_CASES)) with _ -> None) ts in
  (K eth THENC
   PURE_ONCE_REWRITE_CONV(x86_execute_case_rules) THENC
   REWRITE_CONV[add_store_event;add_load_event;SEQ_ID] THENC
   ONCE_DEPTH_CONV OPERAND_SIZE_CONV THENC
   REWRITE_CONV[condition_semantics; aligned_OPERAND128; aligned_OPERAND256] THENC
   REWRITE_CONV[OPERAND_SIZE_CASES] THENC
   REWRITE_CONV[OPERAND_CLAUSES] THENC
   ONCE_DEPTH_CONV BSID_SEMANTICS_CONV THENC
   REWRITE_CONV X86_OPERATION_CLAUSES THENC
   REWRITE_CONV[READ_RVALUE;
                ASSIGN_ZEROTOP_32; READ_ZEROTOP_32; WRITE_ZEROTOP_32;
                ASSIGN_ZEROTOP_128; READ_ZEROTOP_128; WRITE_ZEROTOP_128;
                READ_BOTTOM_128] THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC
   REWRITE_CONV[SEQ; condition_semantics] THENC
   REWRITE_CONV[bytesize] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV
    [UNDEFINED_VALUE; UNDEFINED_VALUES; SEQ_ID] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV
    [ASSIGNS_PULL_ZEROTOP_THM; ASSIGNS_PULL_THM] THENC
   REWRITE_CONV[ASSIGNS_THM] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [SEQ_PULL_THM; BETA_THM] THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV[assign; seq; UNWIND_THM1; BETA_THM] THENC
   TRY_CONV(REWRITE_CONV[WRITE_BOTTOM_128]) THENC
   TRY_CONV(REWRITE_CONV READ_YMM_SSE_EQUIV) THENC
   REWRITE_CONV[] THENC REWRITE_CONV[WRITE_SHORT; READ_SHORT] THENC
   TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
   X86_FORCE_CONDITIONAL_CONV ths THENC
   ONCE_DEPTH_CONV
    (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
     GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
     RAND_CONV NUM_REDUCE_CONV) THENC
   TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
   GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
   GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL] THENC
   ONCE_DEPTH_CONV WORD_PC_PLUS_CONV THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC
   ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV
 ) tm;;

let X86_BASIC_STEP_TAC =
  let x86_tm = `x86` and x86_ty = `:x86state` and one = `1:num` in
  fun (decode_ths: thm option array) sname store_inst_term_to (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,x86_ty) in
    let atm = mk_comb(mk_comb(x86_tm,sv),sv') in
    let eth = X86_CONV decode_ths (map snd asl) atm in
    (match store_inst_term_to with
     | Some r -> r := rhs (concl eth)
     | None -> ());
    let progress_tac =
      let c,_ = strip_comb w in
      if name_of c = "eventually" then
        GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC
      else if name_of c = "eventually_n" then
        let stepn = dest_numeral(rand(rator(rator w))) in
        let stepn_decr = stepn -/ num 1 in
        let stepn_thm = GSYM (NUM_ADD_CONV
          (mk_binary "+" (one,mk_numeral(stepn_decr)))) in
        GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [stepn_thm] THEN
        GEN_REWRITE_TAC I [EVENTUALLY_N_STEP]
      else failwith "X86_BASIC_STEP_TAC: neither eventually nor eventually_n"
      in
    (progress_tac THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN
      (CONV_TAC EXISTS_NONTRIVIAL_CONV ORELSE
        (PRINT_GOAL_TAC THEN
        FAIL_TAC ("X86_BASIC_STEP_TAC: Equality between two states is " ^
                  "ill-formed. Did you forget to assume an extra condition" ^
                  " like pointer alignment?")));
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth] THEN
      REPEAT X86_UNDEFINED_CHOOSE_TAC]) (asl,w);;

let X86_STEP_TAC (mc_length_th,decode_ths) subths sname
      (store_inst_term_to: term ref option)
      (strip_component_tac: thm_tactic) =
  X86_BASIC_STEP_TAC decode_ths sname store_inst_term_to THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP bytes_loaded_update mc_length_th) THEN
  MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o
    MATCH_MP bytes_loaded_update o CONJUNCT1) subths THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    strip_component_tac th);;

let X86_VERBOSE_STEP_TAC (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  X86_STEP_TAC (exth1,exth2) [] sname None (K STRIP_TAC) g;;

let X86_SINGLE_STEP_TAC th s =
  time (X86_VERBOSE_STEP_TAC th s) THEN
  DISCARD_OLDSTATE_TAC s THEN
  CLARIFY_TAC;;

let X86_STEPS_TAC th snums =
  MAP_EVERY (X86_SINGLE_STEP_TAC th) (statenames "s" snums);;

(*** print_literal_from_elf "x86_64/mldsa/rej_uniform_eta4_avx2_asm.o";;
 ***)

let mldsa_rej_uniform_eta4_mc = define_assert_from_elf
  "mldsa_rej_uniform_eta4_mc" "x86_64/mldsa/rej_uniform_eta4_avx2_asm.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x41; 0xb8; 0x0f; 0x0f; 0x0f; 0x0f;
                           (* MOV (% r8d) (Imm32 (word 252645135)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xd0;
                           (* VMOVD (%_% xmm2) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0x41; 0xb8; 0x04; 0x04; 0x04; 0x04;
                           (* MOV (% r8d) (Imm32 (word 67372036)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xd8;
                           (* VMOVD (%_% xmm3) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0x41; 0xb8; 0x09; 0x09; 0x09; 0x09;
                           (* MOV (% r8d) (Imm32 (word 151587081)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xe0;
                           (* VMOVD (%_% xmm4) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x0f; 0x87; 0xfb; 0x00; 0x00; 0x00;
                           (* JA (Imm32 (word 251)) *)
  0x81; 0xf9; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% ecx) (Imm32 (word 256)) *)
  0x0f; 0x87; 0xef; 0x00; 0x00; 0x00;
                           (* JA (Imm32 (word 239)) *)
  0xc4; 0xe2; 0x7d; 0x30; 0x04; 0x0e;
                           (* VPMOVZXBW (%_% ymm0) (Memop Word128 (%%% (rsi,0,rcx))) *)
  0xc5; 0xf5; 0x71; 0xf0; 0x04;
                           (* VPSLLW (%_% ymm1) (%_% ymm0) (Imm8 (word 4)) *)
  0xc5; 0xfd; 0xeb; 0xc1;  (* VPOR (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xdb; 0xc2;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xf8; 0xcc;  (* VPSUBB (%_% ymm1) (%_% ymm0) (%_% ymm4) *)
  0xc5; 0xe5; 0xf8; 0xc0;  (* VPSUBB (%_% ymm0) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0x7d; 0xd7; 0xc1;  (* VPMOVMSKB (% r8d) (%_% ymm1) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xc5; 0x00;
                           (* VEXTRACTI128 (%_% xmm5) (%_% ymm0) (Imm8 (word 0)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x34; 0xd2;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0xe2; 0x51; 0x00; 0xf6;
                           (* VPSHUFB (%_% xmm6) (%_% xmm5) (%_% xmm6) *)
  0xc4; 0xe2; 0x7d; 0x21; 0xce;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm6) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x0f; 0x87; 0x97; 0x00; 0x00; 0x00;
                           (* JA (Imm32 (word 151)) *)
  0xc5; 0xd1; 0x73; 0xdd; 0x08;
                           (* VPSRLDQ (%_% xmm5) (%_% xmm5) (Imm8 (word 8)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x34; 0xd2;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0xe2; 0x51; 0x00; 0xf6;
                           (* VPSHUFB (%_% xmm6) (%_% xmm5) (%_% xmm6) *)
  0xc4; 0xe2; 0x7d; 0x21; 0xce;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm6) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x77; 0x63;              (* JA (Imm8 (word 99)) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xc5; 0x01;
                           (* VEXTRACTI128 (%_% xmm5) (%_% ymm0) (Imm8 (word 1)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x34; 0xd2;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0xe2; 0x51; 0x00; 0xf6;
                           (* VPSHUFB (%_% xmm6) (%_% xmm5) (%_% xmm6) *)
  0xc4; 0xe2; 0x7d; 0x21; 0xce;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm6) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x77; 0x2e;              (* JA (Imm8 (word 46)) *)
  0xc5; 0xd1; 0x73; 0xdd; 0x08;
                           (* VPSRLDQ (%_% xmm5) (%_% xmm5) (Imm8 (word 8)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x34; 0xd2;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0xe2; 0x51; 0x00; 0xf6;
                           (* VPSHUFB (%_% xmm6) (%_% xmm5) (%_% xmm6) *)
  0xc4; 0xe2; 0x7d; 0x21; 0xce;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm6) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0xe9; 0xfa; 0xfe; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294967034)) *)
  0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 256)) *)
  0x73; 0x51;              (* JAE (Imm8 (word 81)) *)
  0x81; 0xf9; 0x10; 0x01; 0x00; 0x00;
                           (* CMP (% ecx) (Imm32 (word 272)) *)
  0x73; 0x49;              (* JAE (Imm8 (word 73)) *)
  0x44; 0x0f; 0xb6; 0x1c; 0x0e;
                           (* MOVZX (% r11d) (Memop Byte (%%% (rsi,0,rcx))) *)
  0xff; 0xc1;              (* INC (% ecx) *)
  0x45; 0x89; 0xda;        (* MOV (% r10d) (% r11d) *)
  0x41; 0x83; 0xe2; 0x0f;  (* AND (% r10d) (Imm8 (word 15)) *)
  0x41; 0x83; 0xfa; 0x09;  (* CMP (% r10d) (Imm8 (word 9)) *)
  0x73; 0x16;              (* JAE (Imm8 (word 22)) *)
  0x41; 0xb9; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 4)) *)
  0x45; 0x29; 0xd1;        (* SUB (% r9d) (% r10d) *)
  0x44; 0x89; 0x0c; 0x87;  (* MOV (Memop Doubleword (%%% (rdi,2,rax))) (% r9d) *)
  0xff; 0xc0;              (* INC (% eax) *)
  0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 256)) *)
  0x73; 0x1f;              (* JAE (Imm8 (word 31)) *)
  0x41; 0xc1; 0xeb; 0x04;  (* SHR (% r11d) (Imm8 (word 4)) *)
  0x41; 0x83; 0xe3; 0x0f;  (* AND (% r11d) (Imm8 (word 15)) *)
  0x41; 0x83; 0xfb; 0x09;  (* CMP (% r11d) (Imm8 (word 9)) *)
  0x73; 0xb9;              (* JAE (Imm8 (word 185)) *)
  0x41; 0xba; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 4)) *)
  0x45; 0x29; 0xda;        (* SUB (% r10d) (% r11d) *)
  0x44; 0x89; 0x14; 0x87;  (* MOV (Memop Doubleword (%%% (rdi,2,rax))) (% r10d) *)
  0xff; 0xc0;              (* INC (% eax) *)
  0xeb; 0xa8;              (* JMP (Imm8 (word 168)) *)
  0xc3                     (* RET *)
];;

(* The trimmed version (without leading ENDBR64) is what loads at the entry pc. *)
let mldsa_rej_uniform_eta4_tmc = define_trimmed
  "mldsa_rej_uniform_eta4_tmc" mldsa_rej_uniform_eta4_mc;;

let MLDSA_REJ_UNIFORM_ETA4_EXEC = X86_MK_CORE_EXEC_RULE mldsa_rej_uniform_eta4_tmc;;

(* ------------------------------------------------------------------------- *)
(* Length helpers                                                            *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC =
  REWRITE_CONV[mldsa_rej_uniform_eta4_tmc] `LENGTH mldsa_rej_uniform_eta4_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

(* ------------------------------------------------------------------------- *)
(* Supporting spec lemmas, byte-shape interior aliases.                      *)
(*                                                                           *)
(* The public spec REJ_SAMPLE_ETA4 (in common/mldsa_specs.ml) takes a        *)
(* nibble list. The proof below is naturally written against the byte-list  *)
(* shape, since the loop invariant peels off bytes per iteration, so we     *)
(* introduce private byte-shape aliases below and bridge to the public spec *)
(* at the subroutine spec.                                                  *)
(* ------------------------------------------------------------------------- *)

let REJ_NIBBLES_ETA4 = define
  `REJ_NIBBLES_ETA4 (l:byte list) =
   FILTER (\x:int16. val x < 9) (NIBBLES_OF_BYTES l)`;;

let REJ_SAMPLE_ETA4_BYTES = define
  `REJ_SAMPLE_ETA4_BYTES (l:byte list) =
   MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32)
       (REJ_NIBBLES_ETA4 l)`;;

(* Conversion lemma: NIBBLES_OF_BYTES (int16 list) = MAP word_zx of BYTES_TO_NIBBLES (4 word list) *)
let NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES = prove
 (`!l:byte list.
     NIBBLES_OF_BYTES l = MAP (\x:4 word. word_zx x:int16) (BYTES_TO_NIBBLES l)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[NIBBLES_OF_BYTES; BYTES_TO_NIBBLES; MAP]; ALL_TAC] THEN
  REWRITE_TAC[NIBBLES_OF_BYTES; BYTES_TO_NIBBLES; MAP; APPEND] THEN
  ASM_REWRITE_TAC[NIBBLE_PAIR; MAP; APPEND] THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_4; DIMINDEX_16; word_zx] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REPEAT AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(GSYM MOD_LT) THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* Bridge: byte-shape composition equals the public nibble-list spec        *)
(* applied to BYTES_TO_NIBBLES. Used only at the subroutine-spec boundary. *)
let REJ_SAMPLE_ETA4_BYTES_EQ = prove
 (`!l:byte list. REJ_SAMPLE_ETA4_BYTES l =
                 REJ_SAMPLE_ETA4 (BYTES_TO_NIBBLES l)`,
  GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4; REJ_SAMPLE_ETA4;
              NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES] THEN
  REWRITE_TAC[FILTER_MAP; o_DEF; GSYM MAP_o] THEN
  SUBGOAL_THEN `!x:4 word. val (word_zx x:int16) = val x`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
    REWRITE_TAC[DIMINDEX_4; DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`BYTES_TO_NIBBLES (l:byte list)`,`xs:(4 word) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  BITBLAST_TAC);;

let REJ_NIBBLES_ETA4_EMPTY = prove
 (`REJ_NIBBLES_ETA4 [] = []`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; FILTER]);;

let REJ_NIBBLES_ETA4_APPEND = prove
 (`!l1 l2. REJ_NIBBLES_ETA4(APPEND l1 l2) =
           APPEND (REJ_NIBBLES_ETA4 l1) (REJ_NIBBLES_ETA4 l2)`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES_APPEND; FILTER_APPEND]);;

(* Loop step: peel off 16 bytes per iteration. Used in loop body. *)
let REJ_NIBBLES_ETA4_STEP_16 = prove
 (`!inlist:byte list. !i:num.
   16 * (i + 1) <= LENGTH inlist
   ==> REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i + 1)) inlist) =
       APPEND (REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * i) inlist))
              (REJ_NIBBLES_ETA4(SUB_LIST(16 * i, 16) inlist))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REJ_NIBBLES_ETA4_APPEND] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `16 * (i + 1) = 0 + 16 * i + 16` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES]);;

(* Length bound on filtered nibbles - used for ABBREV bounds *)
let LENGTH_REJ_NIBBLES_ETA4 = prove
 (`!l:byte list. LENGTH(REJ_NIBBLES_ETA4 l) <= 2 * LENGTH l`,
  GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4] THEN
  TRANS_TAC LE_TRANS `LENGTH(NIBBLES_OF_BYTES l:int16 list)` THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH_FILTER]; ALL_TAC] THEN
  SPEC_TAC(`l:byte list`,`l:byte list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; LENGTH; NIBBLE_PAIR;
                  APPEND; LENGTH_APPEND; LE_0] THEN
  UNDISCH_TAC `LENGTH(NIBBLES_OF_BYTES t:int16 list) <=
               2 * LENGTH(t:byte list)` THEN ARITH_TAC);;

(* Length bound for a 16-byte chunk: each byte yields up to 2 nibbles, *)
(* so REJ_NIBBLES_ETA4 on a 16-byte chunk has length at most 32. *)
let LENGTH_REJ_NIBBLES_ETA4_16 = prove
 (`!inlist:byte list. !i:num.
     16 * (i + 1) <= LENGTH inlist
     ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 16) inlist):int16 list) <= 32`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(16*i, 16) inlist:byte list` LENGTH_REJ_NIBBLES_ETA4) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* Monotonicity: outlen for sub-list at i+1 is >= outlen at i. *)
(* Used to derive that intermediate sub-iter outlen <= final outlen. *)
let LENGTH_REJ_NIBBLES_ETA4_MONO = prove
 (`!inlist:byte list. !i:num.
     16 * (i + 1) <= LENGTH inlist
     ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*i) inlist):int16 list) <=
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(i+1)) inlist):int16 list)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LE_ADD]);;

(* General prefix monotonicity of the accepted-nibble count: a shorter      *)
(* input prefix accepts no more nibbles than a longer one. (niblen is       *)
(* FILTER of NIBBLES_OF_BYTES, both monotone under list prefix.) Used to    *)
(* derive the intra-block sub-iter bounds from the binding end-of-block     *)
(* bound -- the clean-block control-flow argument: the SIMD loop has three  *)
(* mid-iteration `ja` early-exits (after sub-iters 1,2,3), and a block runs *)
(* to completion (loops back) exactly when niblen at its END (offset        *)
(* 16*j+12 covering all but the last sub-iter's stores; the 4th adds no     *)
(* further guard) stays <= 248; this lemma propagates that bound to the     *)
(* earlier sub-iter checkpoints so all three mid-iter ja's fall through.    *)
let NIBLEN_PREFIX_MONO = prove
 (`!l:byte list a b. a <= b
     ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,a) l):int16 list) <=
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,b) l):int16 list)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUB_LIST(0,b) (l:byte list) =
                APPEND (SUB_LIST(0,a) l) (SUB_LIST(a,b-a) l)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:byte list`; `a:num`; `b - a`; `0`] SUB_LIST_SPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE `a <= b ==> a + (b - a) = b`; ADD_CLAUSES];
    REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN ARITH_TAC]);;

(* For a clean block j (entry guard 16*j <= 256 passes and the end-of-block *)
(* count niblen(16*j+12) <= 248), all three mid-iteration ctr-guards (at    *)
(* checkpoints 16*j, 16*j+4, 16*j+8) are <= 248 too, so every mid-iter `ja` *)
(* falls through and the block's four sub-iters all execute -- the loop     *)
(* then re-tests at the head. Direct consequence of NIBLEN_PREFIX_MONO.     *)
let CLEAN_BLOCK_BOUNDS = prove
 (`!inlist:byte list j.
     16 * j <= 256 /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*j+12) inlist):int16 list) <= 248
     ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*j) inlist):int16 list) <= 248 /\
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*j+4) inlist):int16 list) <= 248 /\
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*j+8) inlist):int16 list) <= 248`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  TRANS_TAC LE_TRANS
    `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*j+12) inlist):int16 list)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ARITH_TAC);;

(* Bridge: relate val (word_zx of byte) < 9 to val byte < 9, useful for *)
(* the popcnt-to-FILTER bridge in each sub-iter.                        *)
let VAL_WORD_ZX_BYTE_LT_9 = prove
 (`!b:byte. (val (word_zx b:int16) < 9) <=> (val b < 9)`,
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16] THEN ARITH_TAC);;

(* Bridge from popcnt of low 8 bits of mask to LENGTH of FILTER on the *)
(* corresponding 8 nibbles. The mask bit pattern is set via vpsubb     *)
(* (bound - nibble), so bit 7 of byte k is set iff nibble_k < bound=9. *)
(* This says: bitval-sum for 8 conditions equals LENGTH(FILTER ...).   *)
let FILTER_LT_9_LENGTH_8 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte)
    (b4:byte) (b5:byte) (b6:byte) (b7:byte).
     LENGTH(FILTER (\x:int16. val x < 9)
                   [word_zx b0; word_zx b1; word_zx b2; word_zx b3;
                    word_zx b4; word_zx b5; word_zx b6; word_zx b7]) =
     bitval (val b0 < 9) + bitval (val b1 < 9) +
     bitval (val b2 < 9) + bitval (val b3 < 9) +
     bitval (val b4 < 9) + bitval (val b5 < 9) +
     bitval (val b6 < 9) + bitval (val b7 < 9)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(b0:byte) < 9`; `val(b1:byte) < 9`;
    `val(b2:byte) < 9`; `val(b3:byte) < 9`;
    `val(b4:byte) < 9`; `val(b5:byte) < 9`;
    `val(b6:byte) < 9`; `val(b7:byte) < 9`] THEN
  ASM_REWRITE_TAC[FILTER; LENGTH; bitval; ADD_CLAUSES;
                  VAL_WORD_ZX_BYTE_LT_9] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* For a 4-byte chunk, the LENGTH of REJ_NIBBLES_ETA4 = sum of bitvals  *)
(* over the 8 nibbles (low and high of each of the 4 bytes).            *)
(* This is the LENGTH side of each sub-iter (8 nibbles per sub-iter).   *)
(* Note: the proof uses the int16-stored val form which equals          *)
(* val of byte mod/div 16 (since val MOD 16 < 16 < 65536 fits).        *)
let LENGTH_REJ_NIBBLES_ETA4_4_BYTES = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list) =
     bitval (val(word(val b0 MOD 16):int16) < 9) +
     bitval (val(word(val b0 DIV 16):int16) < 9) +
     bitval (val(word(val b1 MOD 16):int16) < 9) +
     bitval (val(word(val b1 DIV 16):int16) < 9) +
     bitval (val(word(val b2 MOD 16):int16) < 9) +
     bitval (val(word(val b2 DIV 16):int16) < 9) +
     bitval (val(word(val b3 MOD 16):int16) < 9) +
     bitval (val(word(val b3 DIV 16):int16) < 9)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND] THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(word(val(b0:byte) MOD 16):int16) < 9`;
    `val(word(val(b0:byte) DIV 16):int16) < 9`;
    `val(word(val(b1:byte) MOD 16):int16) < 9`;
    `val(word(val(b1:byte) DIV 16):int16) < 9`;
    `val(word(val(b2:byte) MOD 16):int16) < 9`;
    `val(word(val(b2:byte) DIV 16):int16) < 9`;
    `val(word(val(b3:byte) MOD 16):int16) < 9`;
    `val(word(val(b3:byte) DIV 16):int16) < 9`] THEN
  ASM_REWRITE_TAC[FILTER; LENGTH; bitval; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The total accepted nibble count over a 16-byte chunk equals the sum  *)
(* of accepted-counts over each of the 4 four-byte sub-chunks.          *)
let LENGTH_REJ_NIBBLES_ETA4_16_BYTES_SPLIT = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte)
    (b4:byte) (b5:byte) (b6:byte) (b7:byte)
    (b8:byte) (b9:byte) (b10:byte) (b11:byte)
    (b12:byte) (b13:byte) (b14:byte) (b15:byte).
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7;
                              b8;b9;b10;b11;b12;b13;b14;b15]:int16 list) =
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list) +
     LENGTH(REJ_NIBBLES_ETA4 [b4;b5;b6;b7]:int16 list) +
     LENGTH(REJ_NIBBLES_ETA4 [b8;b9;b10;b11]:int16 list) +
     LENGTH(REJ_NIBBLES_ETA4 [b12;b13;b14;b15]:int16 list)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `[b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]:byte list =
    APPEND [b0;b1;b2;b3]
     (APPEND [b4;b5;b6;b7]
       (APPEND [b8;b9;b10;b11] [b12;b13;b14;b15]))`
  SUBST1_TAC THENL [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN
  ARITH_TAC);;

(* SUB_ITER_TAC: processes one of the 4 sub-iterations.                *)
(* Parameters:                                                          *)
(*   start   - state index where this sub-iter begins (e.g. 35 for k=2) *)
(*   stop    - state index where this sub-iter ends (e.g. 47 for k=2)   *)
(*   sub_pc  - PC offset where this sub-iter's first instr is located   *)
(*   end_pc  - PC offset of the cmp-eax-0xf8 (after popcntl/add/shr/add)*)
(*   k       - sub-iter index (0..3): 0 uses extracted xmm5 directly;   *)
(*             1 uses vpsrldq xmm5,8; 2 uses vextracti128 $1; 3 uses    *)
(*             vpsrldq xmm5,8 again                                     *)
(*   chunk_off - byte offset within the 16-byte block (0, 4, 8, or 12)  *)
(*                                                                      *)
(* This tactic is conceptual; calling it requires the full pipeline of  *)
(* (1) establish RIP=word(pc + sub_pc) via JA-not-taken,                *)
(* (2) X86_STEPS_TAC stop-start instructions,                           *)
(* (3) bridge popcnt -> LENGTH FILTER via FILTER_LT_9_LENGTH_8,         *)
(* (4) bridge vmovdqu store data -> num_of_wordlist of accepted nibbles *)
(*     (an 8-way ASM_CASES_TAC + WORD_BLAST per mlkem line 728-784),    *)
(* (5) update outlen invariant: outlen' = outlen + popcnt_k.            *)
(* These are too dependent on local state to abstract cleanly, but the *)
(* shape is identical for k=0..3.                                       *)

(* REJ_SAMPLE_ETA4_BYTES decomposition: append on lists. *)
let REJ_SAMPLE_ETA4_BYTES_APPEND = prove
 (`!l1 l2:byte list. REJ_SAMPLE_ETA4_BYTES (APPEND l1 l2) =
                     APPEND (REJ_SAMPLE_ETA4_BYTES l1) (REJ_SAMPLE_ETA4_BYTES l2)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4_APPEND;
              MAP_APPEND]);;

(* REJ_SAMPLE_ETA4_BYTES step over 16 bytes, used for outlist evolution. *)
let REJ_SAMPLE_ETA4_BYTES_STEP_16 = prove
 (`!inlist:byte list. !i:num.
   16 * (i + 1) <= LENGTH inlist
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16 * (i + 1)) inlist) =
       APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16 * i) inlist))
              (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(16 * i, 16) inlist))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REJ_SAMPLE_ETA4_BYTES_APPEND] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `16 * (i + 1) = 0 + 16 * i + 16` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES]);;

(* The bytes of a 16-byte chunk decompose into 4 four-byte sub-chunks.    *)
(* Each sub-iter processes one such 4-byte sub-chunk via the table lookup *)
(* + pshufb pipeline.                                                     *)
let REJ_SAMPLE_ETA4_BYTES_16_AS_4 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte)
    (b4:byte) (b5:byte) (b6:byte) (b7:byte)
    (b8:byte) (b9:byte) (b10:byte) (b11:byte)
    (b12:byte) (b13:byte) (b14:byte) (b15:byte).
     REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3;b4;b5;b6;b7;
                            b8;b9;b10;b11;b12;b13;b14;b15] =
     APPEND (REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3])
       (APPEND (REJ_SAMPLE_ETA4_BYTES [b4;b5;b6;b7])
         (APPEND (REJ_SAMPLE_ETA4_BYTES [b8;b9;b10;b11])
                 (REJ_SAMPLE_ETA4_BYTES [b12;b13;b14;b15])))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `[b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]:byte list =
    APPEND [b0;b1;b2;b3]
     (APPEND [b4;b5;b6;b7]
       (APPEND [b8;b9;b10;b11] [b12;b13;b14;b15]))`
  SUBST1_TAC THENL [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND]);;

(* For sub-iter k (0 <= k <= 3), the contribution to outlen is *)
(* LENGTH(REJ_NIBBLES_ETA4 [b_(4k); ...; b_(4k+3)])           *)
(* Equivalently in int32 form:                                 *)
(* LENGTH(REJ_SAMPLE_ETA4_BYTES [b_(4k); ...; b_(4k+3)])      *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES = prove
 (`!l:byte list.
     LENGTH(REJ_SAMPLE_ETA4_BYTES l:int32 list) =
     LENGTH(REJ_NIBBLES_ETA4 l:int16 list)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; LENGTH_MAP]);;

(* Strict bound on REJ_NIBBLES_ETA4 length per byte: each byte produces  *)
(* at most 2 accepted nibbles. Useful for sub-iter bound proofs.        *)
let LENGTH_REJ_NIBBLES_ETA4_PER_BYTE = prove
 (`!b:byte. LENGTH(REJ_NIBBLES_ETA4 [b]:int16 list) <= 2`,
  GEN_TAC THEN
  MP_TAC(SPEC `[b]:byte list` LENGTH_REJ_NIBBLES_ETA4) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* For 4 bytes, at most 8 accepted nibbles. *)
let LENGTH_REJ_NIBBLES_ETA4_4 = prove
 (`!l:byte list. LENGTH l = 4 ==> LENGTH(REJ_NIBBLES_ETA4 l:int16 list) <= 8`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `l:byte list` LENGTH_REJ_NIBBLES_ETA4) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* The popcnt of the low byte of any int32 is at most 8. Used to bound    *)
(* the increment to RAX from popcntl in each sub-iteration.               *)
let WORD_POPCOUNT_LOW8_LE_8 = prove
 (`!w:int32. word_popcount(word_zx (word_subword w (0,8):byte):int32) <= 8`,
  GEN_TAC THEN
  MATCH_MP_TAC WORD_POPCOUNT_BOUND_SIZE THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* val of (word(popcnt low 8 bits)) is bounded by 8. Used as the popcnt    *)
(* bound for sub-iter writeback vmovdqu nonoverlap proofs.                  *)
let VAL_WORD_POPCOUNT_LOW8_LE_8 = prove
 (`!w:int32. val(word(word_popcount(word_zx (word_subword w (0,8):byte):int32)):int32) <= 8`,
  GEN_TAC THEN
  MP_TAC(SPEC `w:int32` WORD_POPCOUNT_LOW8_LE_8) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `word_popcount(word_zx (word_subword (w:int32) (0,8):byte):int32) MOD 2 EXP 32 =
    word_popcount(word_zx (word_subword (w:int32) (0,8):byte):int32)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `word_popcount(word_zx (word_subword (w:int32) (0,8):byte):int32) <= 8` THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 32 = 4294967296`] THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* RAX-after-popcnt-add bridge: the asm `add eax, r9d` after popcnt produces *)
(* RAX = word_zx(word_add(word_zx(word outlen)) (word_zx pcnt)). When        *)
(* outlen <= 248 (loop-head precondition) and val pcnt <= 8 (popcnt bound),  *)
(* this equals word(outlen + val pcnt) and the sum is bounded by 256,       *)
(* enabling the subsequent vmovdqu's nonoverlap proof.                       *)
let RAX_BOUND_AFTER_POPCNT_ADD = prove
 (`!outlen:num pcnt:int32.
     outlen <= 248 /\ val pcnt <= 8
     ==> (word_zx (word_add (word_zx (word outlen:int32):int32) (word_zx pcnt:int32):int32):int64) =
         word(outlen + val pcnt) /\
         outlen + val pcnt <= 256`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD] THEN
    SUBGOAL_THEN `outlen MOD 2 EXP 32 = outlen /\
                  val(pcnt:int32) MOD 2 EXP 32 = val pcnt`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THENL
       [UNDISCH_TAC `outlen <= 248` THEN
        REWRITE_TAC[ARITH_RULE `2 EXP 32 = 4294967296`] THEN ARITH_TAC;
        MP_TAC(ISPEC `pcnt:int32` VAL_BOUND) THEN
        REWRITE_TAC[DIMINDEX_32]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(outlen + val(pcnt:int32)) MOD 2 EXP 32 = outlen + val pcnt`
      SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `outlen <= 248` THEN UNDISCH_TAC `val(pcnt:int32) <= 8` THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 32 = 4294967296`] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(outlen + val(pcnt:int32)) MOD 2 EXP 64 = outlen + val pcnt`
      SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `outlen <= 248` THEN UNDISCH_TAC `val(pcnt:int32) <= 8` THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`] THEN ARITH_TAC;
      REFL_TAC];
    UNDISCH_TAC `outlen <= 248` THEN UNDISCH_TAC `val(pcnt:int32) <= 8` THEN
    ARITH_TAC]);;

(* Generic int32 word_zx(word_add(word_zx(word a), word_zx(word b))) = word(a+b) *)
(* when a+b fits in int32. Used at every sub-iter boundary for both the   *)
(* outlen-tracking RAX accumulator and the RCX position counter.          *)
let RAX_BOUND_GENERIC = prove
 (`!a:num b:num.
     a + b < 2 EXP 32
     ==> (word_zx (word_add (word_zx (word a:int32):int32) (word_zx (word b:int32):int32):int32):int64) =
         word(a + b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD] THEN
  SUBGOAL_THEN `a MOD 2 EXP 32 = a /\ b MOD 2 EXP 32 = b`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `a + b < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_LT THEN
  UNDISCH_TAC `a + b < 2 EXP 32` THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`;
              ARITH_RULE `2 EXP 32 = 4294967296`] THEN ARITH_TAC);;

(* Direct bridge for the actual asm RAX form after `add eax, r9d` where  *)
(* r9 = popcntl r10d (and r10d came from movzx r10d, r8b — bounded by    *)
(* 256). The simulator produces RAX with two nested word_zx wrappers     *)
(* (one from popcntl int32 result wrapping into int64). This bridge      *)
(* takes the bound `val x < 2 EXP 8` directly (from movzx semantics)     *)
(* and produces the canonical `word(outlen + n) /\ outlen + n <= 256`.   *)
let RAX_BOUND_AFTER_POPCNT_ADD_DIRECT = prove
 (`!outlen:num x:int64.
     outlen <= 248 /\ val(x:int64) < 2 EXP 8
     ==> ?n. n <= 8 /\
             word_zx (word_add (word_zx (word outlen:int32):int32)
                               (word_zx (word_zx (word(word_popcount(word_zx x:int32)):int32):int32):int32):int32):int64 =
             word(outlen + n):int64 /\
             outlen + n <= 256`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_popcount(word_zx (x:int64):int32) <= 8`
    ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_POPCOUNT_BOUND_SIZE THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
    SUBGOAL_THEN `val(x:int64) MOD 2 EXP 32 = val x` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `val(x:int64) < 2 EXP 8` THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `val(x:int64) < 2 EXP 8` THEN ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `word_popcount(word_zx (x:int64):int32)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD] THEN
  SUBGOAL_THEN
   `outlen MOD 2 EXP 32 = outlen /\
    word_popcount(word_zx (x:int64):int32) MOD 2 EXP 32 =
    word_popcount(word_zx (x:int64):int32)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THENL
    [UNDISCH_TAC `outlen <= 248` THEN
     REWRITE_TAC[ARITH_RULE `2 EXP 32 = 4294967296`] THEN ARITH_TAC;
     UNDISCH_TAC `word_popcount(word_zx (x:int64):int32) <= 8` THEN
     REWRITE_TAC[ARITH_RULE `2 EXP 32 = 4294967296`] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(outlen + word_popcount(word_zx (x:int64):int32)) MOD 2 EXP 32 =
    outlen + word_popcount(word_zx (x:int64):int32)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `outlen <= 248` THEN
    UNDISCH_TAC `word_popcount(word_zx (x:int64):int32) <= 8` THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 32 = 4294967296`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(outlen + word_popcount(word_zx (x:int64):int32)) MOD 2 EXP 64 =
    outlen + word_popcount(word_zx (x:int64):int32)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `outlen <= 248` THEN
    UNDISCH_TAC `word_popcount(word_zx (x:int64):int32) <= 8` THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* Chained sub-iter step: combines RAX_BOUND_AFTER_POPCNT_ADD with the    *)
(* popcnt bound to give an existential `?n. n <= 8 /\ RAX_form = word    *)
(* (outlen+n) /\ outlen+n <= 232` directly from the asm's mask-based     *)
(* popcnt expression. This is the per-sub-iter inductive bridge: at      *)
(* each sub-iter k, given outlen <= 248 (loop-head invariant), the post- *)
(* popcnt-add RAX has the canonical form word(outlen + n) where n is the *)
(* per-sub-iter popcount (at most 8 nibbles accepted out of 4 bytes).    *)
let RAX_AFTER_SUB_ITER = prove
 (`!outlen:num mask:int32.
     outlen <= 248
     ==> ?n. n <= 8 /\
             (word_zx (word_add (word_zx (word outlen:int32):int32)
                                (word_zx (word(word_popcount(word_zx (word_subword mask (0,8):byte):int32)):int32):int32)
                                :int32):int64) =
             word(outlen + n) /\
             outlen + n <= 256`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `val(word(word_popcount(word_zx (word_subword (mask:int32) (0,8):byte):int32)):int32)` THEN
  CONJ_TAC THENL [REWRITE_TAC[VAL_WORD_POPCOUNT_LOW8_LE_8]; ALL_TAC] THEN
  MATCH_MP_TAC RAX_BOUND_AFTER_POPCNT_ADD THEN
  ASM_REWRITE_TAC[VAL_WORD_POPCOUNT_LOW8_LE_8]);;

(* word_popcount of a byte expanded as the sum of 8 bit-bitvals.          *)
(* This is the bridge from the popcnt instruction to a per-bit count.    *)
let WORD_POPCOUNT_BYTE = prove
 (`!b:byte. word_popcount b =
            bitval(bit 0 b) + bitval(bit 1 b) + bitval(bit 2 b) +
            bitval(bit 3 b) + bitval(bit 4 b) + bitval(bit 5 b) +
            bitval(bit 6 b) + bitval(bit 7 b)`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_POPCOUNT_NSUM; DIMINDEX_8] THEN
  SUBGOAL_THEN `{i | i < 8} = {0,1,2,3,4,5,6,7}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{0,1,2,3,4,5,6,7} = 0..7` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_NUMSEG; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN ARITH_TAC);;

(* For a byte a with val a < 16 (i.e. nibble-sized), bit 7 of (a - 9)    *)
(* (computed as a byte subtraction) is set iff a < 9.                    *)
(* This is the eta4 analog of VPSUBD_SIGN_BIT_BOUNDED in PR #1014's      *)
(* x86 mldsa_rej_uniform proof — the bridge from VPSUBB to a bit-test.  *)
let VPSUBB_SIGN_BIT_LT_9 = prove
 (`!a:byte. val a < 16
     ==> (bit 7 (word_sub a (word 9):byte) <=> val a < 9)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_VAL; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_8; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(a:byte) < 9` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(val(a:byte) + 247) MOD 256 = val a + 247`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[ODD; ARITH_RULE `ODD 1`] `n = 1 ==> ODD n`) THEN
    MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(a:byte) + 119` THEN ASM_ARITH_TAC;
    REWRITE_TAC[NOT_ODD] THEN
    SUBGOAL_THEN `(val(a:byte) + 247) MOD 256 = val a - 9`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `val(a:byte) + 247 = (val a - 9) + 1 * 256`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[DIV_LT; EVEN] THEN ASM_ARITH_TAC]);;

(* MAJOR BRIDGE (intermediate form): when each bit of mask byte m equals  *)
(* (val byte_k < 9), popcount of m equals LENGTH FILTER on the 8 byte_zx. *)
let POPCOUNT_BYTE_BRIDGE = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte)
    (b4:byte) (b5:byte) (b6:byte) (b7:byte) (m:byte).
     (bit 0 m <=> val b0 < 9) /\ (bit 1 m <=> val b1 < 9) /\
     (bit 2 m <=> val b2 < 9) /\ (bit 3 m <=> val b3 < 9) /\
     (bit 4 m <=> val b4 < 9) /\ (bit 5 m <=> val b5 < 9) /\
     (bit 6 m <=> val b6 < 9) /\ (bit 7 m <=> val b7 < 9)
     ==> word_popcount m =
         LENGTH(FILTER (\x:int16. val x < 9)
                 [word_zx b0; word_zx b1; word_zx b2; word_zx b3;
                  word_zx b4; word_zx b5; word_zx b6; word_zx b7])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FILTER_LT_9_LENGTH_8; WORD_POPCOUNT_BYTE] THEN
  ASM_REWRITE_TAC[]);;

(* The pshufb shuffle-control table, indexed by 8-bit mask m, and the       *)
(* accepted-index list of a mask (its set-bit positions, increasing).       *)
let TABLE_ENTRY = define
 `TABLE_ENTRY (m:byte) = SUB_LIST(8 * val m, 8) (mldsa_rej_uniform_table:byte list)`;;

(* bytes64 read = word of the 8-byte little-endian value. *)
let RB64 = prove
 (`!(a:int64) (s:x86state). read(memory:>bytes64 a) s = word(read(memory:>bytes(a,8)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bytes64; READ_COMPONENT_COMPOSE; asword; through; read]);;

(* Read an n-byte window at offset k of a byte region known to hold num_of_wordlist L:
   the window holds num_of_wordlist(SUB_LIST(k,n) L).  (NB: HOL parses `k + LENGTH L - k`
   as `k + (LENGTH L - k)` since `-` binds tighter than `+`; the SUB_ADD-style reductions
   here go through ASM_ARITH_TAC with the k+n<=LENGTH L hypothesis.) *)
let READ_BYTES_SLICE = prove
 (`!(a:int64) k n (L:byte list) (s:x86state).
      read(memory:>bytes(a,LENGTH L)) s = num_of_wordlist L /\ k + n <= LENGTH L
      ==> read(memory:>bytes(word_add a (word k), n)) s = num_of_wordlist(SUB_LIST(k,n) L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k + (LENGTH(L:byte list) - k) = LENGTH L` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n + (LENGTH(L:byte list) - (k+n)) = LENGTH L - k` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read(memory:>bytes(word_add a (word k), LENGTH(L:byte list) - k)) s =
                num_of_wordlist(SUB_LIST(k, LENGTH L - k) L)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `a:int64`; `s:x86state`;
       `SUB_LIST(0,k) (L:byte list)`; `SUB_LIST(k, LENGTH(L:byte list) - k) L`;
       `k:num`; `LENGTH(L:byte list) - k`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
    REWRITE_TAC[DIMINDEX_8; LENGTH_SUB_LIST; SUB_0] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_LIST_TOPSPLIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `word_add a (word k):int64`; `s:x86state`;
     `SUB_LIST(k,n) (L:byte list)`; `SUB_LIST(k+n, LENGTH(L:byte list) - (k+n)) L`;
     `n:num`; `LENGTH(L:byte list) - (k + n)`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  REWRITE_TAC[DIMINDEX_8; LENGTH_SUB_LIST] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:byte list`; `n:num`; `LENGTH(L:byte list) - (k+n)`; `k:num`] SUB_LIST_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* Store-value bridge (2): the first k int32 lanes of a 256-bit store at address A read
   back as bytes(A,4k) = num_of_wordlist(wordlist_of_num k (val V)).  (k<=8; the vmovdqu
   writeback wrote read(memory:>bytes256 A) = V = the vpmovsxbd output, and the memory
   postcondition reads only the first 4*block_count bytes = the accepted coefficients.)
   Composes with the lane-extract + SUBITER1_VALUE to give num_of_wordlist(REJ_SAMPLE block). *)
let BYTES256_PREFIX_WORDLIST = prove
 (`!(A:int64) (V:int256) k (s:x86state).
      read(memory:>bytes256 A) s = V /\ k <= 8
      ==> read(memory:>bytes(A, 4*k)) s = num_of_wordlist(wordlist_of_num k (val V):int32 list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_OF_NUM; DIMINDEX_32; READ_COMPONENT_COMPOSE] THEN
  SUBGOAL_THEN `read (bytes(A,32)) (read memory (s:x86state)) = val(V:int256)` ASSUME_TAC THENL
   [UNDISCH_TAC `read(memory:>bytes256 A) s = V` THEN
    REWRITE_TAC[bytes256; READ_COMPONENT_COMPOSE; asword; through; read] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VAL_WORD; DIMINDEX_256] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM DIMINDEX_256] THEN
    MP_TAC(ISPECL[`A:int64`;`32`;`read memory (s:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[DIMINDEX_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:int64`; `32`; `4*k`; `read memory (s:x86state)`] READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * k = 32 * k`] THEN
  SUBGOAL_THEN `MIN 32 (4*k) = 4*k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* The j-th lane (j<k<=8) of wordlist_of_num k (val V) is word_subword V (32j,32). *)
let EL_WORDLIST_OF_NUM_VAL = prove
 (`!(V:int256) k j. j < k
     ==> EL j (wordlist_of_num k (val V):int32 list) = word_subword V (32*j,32)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`wordlist_of_num k (val(V:int256)):int32 list`; `j:num`] EL_NUM_OF_WORDLIST) THEN
  REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; NUM_OF_WORDLIST_OF_NUM; DIMINDEX_32] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[word_subword; DIMINDEX_32; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(MESON[] `(word x:int32) = word y ==> word x:int32 = word y`) THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_32] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; MOD_MOD_REFL] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN (32 * k) (32 * j + 32) = 32 * j + 32` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;

(* If V's first k lanes match L's elements (and LENGTH L = k <= 8), the low-k-lane digit
   list of V is exactly L. *)
let WORDLIST_OF_NUM_VAL_EQ = prove
 (`!(V:int256) (L:int32 list) k.
      LENGTH L = k /\ (!j. j < k ==> word_subword V (32*j,32) = EL j L)
      ==> wordlist_of_num k (val V) = L`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_WORDLIST_OF_NUM] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EL_WORDLIST_OF_NUM_VAL] THEN ASM_MESON_TAC[]);;

(* Full-width subword identity (used to close the per-lane vpmovsxbd extraction:
   word_subword (word_sx b:int32) (0,32) = word_sx b, with the word_sx(..) taken as W). *)
let SW_ID = prove(`!W:int32. word_subword W (0,32):int32 = W`, GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* NOTE: in the clean loop body, the stepped vpmovsxbd output `read YMM1 sN` (a word_join
   nest of word_sx over the low-8 bytes of word_zx(word_zx pshuf)) is rewritten to the
   canonical `usimd8 (\b. word_sx b) (word_zx(word_zx pshuf))` form in-context (where the
   term is fully typed by the simulator) via `REWRITE_TAC[usimd8;usimd4;usimd2] THEN
   SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_*;ARITH] THEN CONV_TAC NUM_REDUCE_CONV`, after which
   the committed VPMOVSXBD_LANE_EXTRACT gives each int32 lane = word_sx of the pshuf byte.
   (Validated 2026-06-11; kept as an in-body step rather than a standalone lemma because the
   word_join associativity/widths are simulator-determined.) *)

(* Store-value memory lemma: the first k int32 lanes of a 256-bit store at A read back as
   num_of_wordlist L, where L is the int32 list whose elements are V's lanes.  This is the
   bridge from the vmovdqu writeback to the REJ_SAMPLE block: with V = vpmovsxbd output and
   L = REJ_SAMPLE_ETA4_BYTES block (via SUBITER1_VALUE + VPMOVSXBD_LANE_EXTRACT giving
   word_subword V (32j,32) = EL j L), this yields the sub-iter store memory postcondition. *)
let STORE_BYTES256_NUM_OF_WORDLIST = prove
 (`!(A:int64) (V:int256) (L:int32 list) k (s:x86state).
      read(memory:>bytes256 A) s = V /\ LENGTH L = k /\ k <= 8 /\
      (!j. j < k ==> word_subword V (32*j,32):int32 = EL j L)
      ==> read(memory:>bytes(A, 4*k)) s = num_of_wordlist L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:int64`; `V:int256`; `k:num`; `s:x86state`] BYTES256_PREFIX_WORDLIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC WORDLIST_OF_NUM_VAL_EQ THEN ASM_REWRITE_TAC[]);;

(* The vmovq table load: with the table memory invariant, reading the 8-byte entry at
   index r (byte offset 8r) yields word(num_of_wordlist(TABLE_ENTRY(word r))) — i.e. the
   gather-control word for mask r.  Bridge (1) of the sub-iter store value. *)
let TABLE_VMOVQ_READ = prove
 (`!(table:int64) r (s:x86state).
      read(memory:>bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\ r < 256
      ==> read(memory:>bytes64(word_add table (word(8*r)))) s =
          word(num_of_wordlist(TABLE_ENTRY(word r:byte)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RB64; TABLE_ENTRY] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048` ASSUME_TAC THENL
   [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `val(word r:byte) = r` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`table:int64`; `8*r`; `8`; `mldsa_rej_uniform_table:byte list`; `s:x86state`]
    READ_BYTES_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC]);;

let ACC_IDX = define
 `ACC_IDX (m:byte) = FILTER (\i. bit i m) [0;1;2;3;4;5;6;7]`;;

(* Keystone table-correspondence lemma: for every mask m, the first         *)
(* |ACC_IDX m| bytes of the table entry table[m] are exactly the accepted   *)
(* (set-bit) positions of m, in increasing order. This is what makes the    *)
(* pshufb gather compact the accepted nibbles to the front: gathering the   *)
(* source vector at these table indices reads precisely the accepted lanes. *)
(* Proved by exhaustive 256-mask evaluation (~220s): each case evaluates    *)
(* ACC_IDX(word m) and table[m] concretely and checks the prefix. There is  *)
(* no closed form for the literal 256x8 table, so the case split is honest. *)
let TABLE_PREFIX_ACC = prove
 (`!m. m < 256 ==>
    SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (TABLE_ENTRY(word m)) =
    MAP word (ACC_IDX(word m:byte)):byte list`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[ACC_IDX; TABLE_ENTRY; FILTER] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mldsa_rej_uniform_table] THEN
  CONV_TAC(DEPTH_CONV SUB_LIST_CONV) THEN
  REWRITE_TAC[MAP] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV));;

(* Per-byte VPSHUFB gather behavior: a control byte c with c < 8 (top bit  *)
(* clear, so the byte is selected not zeroed; low nibble = c since c < 8)   *)
(* selects source byte c. This is the building block for the table-driven   *)
(* compaction: the rej_uniform table stores accepted-nibble indices < 8 in  *)
(* each control lane, and this lemma reduces VPSHUFB's f8 selector to a      *)
(* plain source-byte pick. Matches the f8 in x86_VPSHUFB exactly.           *)
let PSHUFB_GATHER_BYTE = prove
 (`!(w:int128) (c:byte). val c < 8
     ==> (if bit 7 c then word 0:byte
          else word_subword w (8 * val (word_subword c (0,4):byte),8)) =
         word_subword w (8 * val c,8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(bit 7 (c:byte))` ASSUME_TAC THENL
   [REWRITE_TAC[BIT_VAL] THEN
    SUBGOAL_THEN `val(c:byte) DIV 2 EXP 7 = 0` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC DIV_LT THEN UNDISCH_TAC `val(c:byte) < 8` THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_subword (c:byte) (0,4):byte) = val c` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `val(c:byte) < 8` THEN ARITH_TAC;
    REFL_TAC]);;

(* Per-lane extraction of a VPSHUFB low-128 result. For any byte->byte lane *)
(* function ff (the f8 selector in x86_VPSHUFB) and a 64-bit control c       *)
(* lifted to 128 by word_zx, the k-th low output byte (k<8) is              *)
(* ff(control-byte k). Proved by unfolding usimd16/8/4/2, routing the       *)
(* word_subword through the nested word_joins with WORD_SUBWORD_JOIN_LOWER/  *)
(* UPPER (the control side is a fixed bit-routing -> WORD_BLAST), and        *)
(* collapsing the outer byte-subword via WORD_SUBWORD_TRIVIAL. Composing     *)
(* this with PSHUFB_GATHER_BYTE (when each control byte < 8) gives the       *)
(* gather g.byte(c.byte k); with TABLE_BYTES_LT_8 the < 8 side condition is  *)
(* automatic for table-sourced controls.                                    *)
let PSHUFB_LANE_EXTRACT = prove
 (`!(ff:byte->byte) (c:int64).
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (0,8):byte = ff(word_subword c (0,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (8,8):byte = ff(word_subword c (8,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (16,8):byte = ff(word_subword c (16,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (24,8):byte = ff(word_subword c (24,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (32,8):byte = ff(word_subword c (32,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (40,8):byte = ff(word_subword c (40,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (48,8):byte = ff(word_subword c (48,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (56,8):byte = ff(word_subword c (56,8))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[usimd16; usimd8; usimd4; usimd2] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  REPEAT CONJ_TAC THEN
  (SIMP_TAC[WORD_SUBWORD_TRIVIAL; DIMINDEX_8; LE_REFL] THEN
   AP_TERM_TAC THEN CONV_TAC WORD_BLAST));;

(* The pshufb control bytes come from the rej_uniform table; every table    *)
(* byte is < 8 (the table stores 8-element index permutations of {0..7}     *)
(* with the unused tail zeroed). Hence in the compaction step every pshufb  *)
(* control lane has its top bit clear and PSHUFB_GATHER_BYTE applies -- the  *)
(* shuffle never zeroes, it always gathers. Proved via ALL over the literal *)
(* table (fast: ~2s) then specialised to EL form.                           *)
let ALL_TABLE_LT_8 = prove
 (`ALL (\b:byte. val b < 8) mldsa_rej_uniform_table`,
  REWRITE_TAC[mldsa_rej_uniform_table; ALL] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let TABLE_BYTES_LT_8 = prove
 (`!j. j < 2048 ==> val(EL j (mldsa_rej_uniform_table:byte list)) < 8`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\b:byte. val b < 8`; `mldsa_rej_uniform_table:byte list`]
                ALL_EL) THEN
  REWRITE_TAC[ALL_TABLE_LT_8] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[]]);;

(* Full VPSHUFB-gather composition: when every control byte of c:int64 is    *)
(* < 8 (true for table-sourced controls by TABLE_BYTES_LT_8), the eight low  *)
(* output bytes of the pshufb gather g at the control byte indices. Combines *)
(* PSHUFB_LANE_EXTRACT (structural lane isolation) with PSHUFB_GATHER_BYTE   *)
(* (per-lane gather). Lane-0 specialisation kept as PSHUFB_TABLE_GATHER for  *)
(* convenience; the indexed PSHUFB_TABLE_GATHER_8 covers all 8 lanes.        *)
let PSHUFB_TABLE_GATHER = prove
 (`!(g:int128) (c:int64).
     (!k. k < 8 ==> val(word_subword c (8*k,8):byte) < 8)
     ==> word_subword (usimd16
            (\(i:byte). if bit 7 i then word 0:byte
                else word_subword g (8 * val(word_subword i (0,4):byte),8))
            (word_zx (word_zx c:int128):int128):int128) (0,8):byte =
         word_subword g (8 * val(word_subword c (0,8):byte),8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PSHUFB_LANE_EXTRACT] THEN
  MATCH_MP_TAC PSHUFB_GATHER_BYTE THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES]);;

let PSHUFB_TABLE_GATHER_8 = prove
 (`!(g:int128) (c:int64).
     (!k. k < 8 ==> val(word_subword c (8*k,8):byte) < 8)
     ==> (!k. k < 8 ==>
            word_subword (usimd16
              (\(i:byte). if bit 7 i then word 0:byte
                  else word_subword g (8 * val(word_subword i (0,4):byte),8))
              (word_zx (word_zx c:int128):int128):int128) (8*k,8):byte =
            word_subword g (8 * val(word_subword c (8*k,8):byte),8))`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[PSHUFB_LANE_EXTRACT] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC PSHUFB_GATHER_BYTE THEN
  ASM_SIMP_TAC[ARITH] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
    MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th) THEN
    MP_TAC(SPEC `6` th) THEN MP_TAC(SPEC `7` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* The vmovq load puts table[m] into an int64 register as                   *)
(* word(num_of_wordlist(TABLE_ENTRY m)); its k-th byte is EL k (TABLE_ENTRY *)
(* m). (Inverse of the little-endian num_of_wordlist packing.)              *)
let CTRL_BYTE_TABLE = prove
 (`!m k. k < 8
     ==> word_subword (word(num_of_wordlist(TABLE_ENTRY m)):int64) (8*k,8):byte
         = EL k (TABLE_ENTRY m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`TABLE_ENTRY m:byte list`; `k:num`]
    (INST_TYPE[`:64`,`:KL`; `:8`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST)) THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_8] THEN
  SUBGOAL_THEN `LENGTH(TABLE_ENTRY m:byte list) = 8` SUBST1_TAC THENL
   [REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST] THEN
    SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Every byte of any table entry is < 8 (from TABLE_BYTES_LT_8 via the      *)
(* SUB_LIST offset arithmetic). So all pshufb control lanes gather.          *)
let TABLE_ENTRY_BYTES_LT_8 = prove
 (`!m k. k < 8 ==> val(EL k (TABLE_ENTRY m):byte) < 8`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TABLE_ENTRY] THEN
  MP_TAC(ISPECL [`mldsa_rej_uniform_table:byte list`; `k:num`; `8 * val(m:byte)`; `8`]
    EL_SUB_LIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC TABLE_BYTES_LT_8 THEN
  MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC);;

(* Full per-output-byte compaction for a table-driven VPSHUFB control: the  *)
(* k-th output byte (k<8) is the source byte g at index EL k (TABLE_ENTRY   *)
(* m). Combines PSHUFB_TABLE_GATHER_8 (gather) + CTRL_BYTE_TABLE (control    *)
(* byte = table entry) + TABLE_ENTRY_BYTES_LT_8 (< 8 side condition). With   *)
(* TABLE_PREFIX_ACC, the first popcount(m) of these are exactly g's bytes   *)
(* at the accepted nibble positions -- i.e. the accepted nibbles compacted. *)
let PSHUFB_OUT_BYTE = prove
 (`!(g:int128) (m:byte) k. k < 8
     ==> word_subword (usimd16
            (\(i:byte). if bit 7 i then word 0:byte
                else word_subword g (8 * val(word_subword i (0,4):byte),8))
            (word_zx (word_zx (word(num_of_wordlist(TABLE_ENTRY m)):int64):int128):int128):int128)
            (8*k,8):byte =
         word_subword g (8 * val(EL k (TABLE_ENTRY m):byte), 8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `word(num_of_wordlist(TABLE_ENTRY m)):int64`]
    PSHUFB_TABLE_GATHER_8) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CTRL_BYTE_TABLE] THEN
    ASM_SIMP_TAC[TABLE_ENTRY_BYTES_LT_8];
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CTRL_BYTE_TABLE]]);;

(* The 8 low output bytes of the table-driven VPSHUFB, as an explicit list, *)
(* and its identification with the gather MAP over the table entry.         *)
let PSHUFB_OUT_LIST = define
 `PSHUFB_OUT_LIST (g:int128) (m:byte) =
    [word_subword g (8 * val(EL 0 (TABLE_ENTRY m):byte),8):byte;
     word_subword g (8 * val(EL 1 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 2 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 3 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 4 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 5 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 6 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 7 (TABLE_ENTRY m):byte),8)]`;;

let PSHUFB_OUT_LIST_AS_MAP = prove
 (`!g m. PSHUFB_OUT_LIST g m =
         MAP (\b:byte. word_subword g (8 * val b,8):byte) (TABLE_ENTRY m)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?a0 a1 a2 a3 a4 a5 a6 a7:byte.
       TABLE_ENTRY m = [a0;a1;a2;a3;a4;a5;a6;a7]` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH(TABLE_ENTRY m:byte list) = 8` MP_TAC THENL
     [REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST] THEN
      SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
        (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`TABLE_ENTRY m:byte list`,`l:byte list`) THEN
    REWRITE_TAC[ARITH_RULE `8 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))`] THEN
    REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[];
    ASM_REWRITE_TAC[PSHUFB_OUT_LIST; MAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]]);;

let SUB_LIST_0_MAP = prove
 (`!(f:A->B) n l. SUB_LIST(0,n) (MAP f l) = MAP f (SUB_LIST(0,n) l)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES; MAP] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES; MAP]);;

(* Nesting/composition of SUB_LIST: a window of width n starting at a, taken from
   a window of width m starting at b, equals the width-n window starting at b+a in
   the original list (provided the inner window covers it and lies inside the list).
   Used to slice the 4-byte sub-iter block SUB_LIST(16i,4) out of the 16-byte chunk
   SUB_LIST(16i,16) when threading per-block facts in the clean loop body. *)
let SUB_LIST_NEST = prove
 (`!a n b m l:A list. a + n <= m /\ b + m <= LENGTH l
     ==> SUB_LIST(a,n)(SUB_LIST(b,m) l) = SUB_LIST(b+a,n) l`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `j < n` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(b,m) (l:A list)) = m` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL j (SUB_LIST(a,n)(SUB_LIST(b,m) (l:A list))) = EL (a+j) (SUB_LIST(b,m) l)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL (a+j) (SUB_LIST(b,m) (l:A list)) = EL (b+(a+j)) l`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL j (SUB_LIST(b+a,n) (l:A list)) = EL ((b+a)+j) l`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* From the 16-byte chunk decomposition SUB_LIST(16i,16) inlist = [chunk0 bytes 0..15],
   extract the four 4-byte sub-iter blocks SUB_LIST(16i+4k,4) inlist (k=0,1,2,3) as the
   corresponding 4-byte slices of chunk0. One application yields all four blocks; the
   clean loop body uses these as the [b0;b1;b2;b3] argument to the per-block popcount /
   REJ_SAMPLE bridges (POPCNT_NIBBLES_4_BYTES_BRIDGE, SUBITER_OUTLEN_STEP_4). *)
let SUBITER_BLOCK_BYTES = prove
 (`!inlist i chunk0:int128.
      16 * i + 16 <= LENGTH(inlist:byte list) /\
      SUB_LIST(16*i,16) inlist =
        [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
         word_subword chunk0 (16,8); word_subword chunk0 (24,8);
         word_subword chunk0 (32,8); word_subword chunk0 (40,8);
         word_subword chunk0 (48,8); word_subword chunk0 (56,8);
         word_subword chunk0 (64,8); word_subword chunk0 (72,8);
         word_subword chunk0 (80,8); word_subword chunk0 (88,8);
         word_subword chunk0 (96,8); word_subword chunk0 (104,8);
         word_subword chunk0 (112,8); word_subword chunk0 (120,8)]
      ==> SUB_LIST(16*i,4) inlist =
            [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
             word_subword chunk0 (16,8); word_subword chunk0 (24,8)] /\
          SUB_LIST(16*i+4,4) inlist =
            [word_subword chunk0 (32,8); word_subword chunk0 (40,8);
             word_subword chunk0 (48,8); word_subword chunk0 (56,8)] /\
          SUB_LIST(16*i+8,4) inlist =
            [word_subword chunk0 (64,8); word_subword chunk0 (72,8);
             word_subword chunk0 (80,8); word_subword chunk0 (88,8)] /\
          SUB_LIST(16*i+12,4) inlist =
            [word_subword chunk0 (96,8); word_subword chunk0 (104,8);
             word_subword chunk0 (112,8); word_subword chunk0 (120,8)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL[`0`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`4`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`8`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`12`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST)] THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[ARITH_RULE `16*i+0 = 16*i`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV SUB_LIST_CONV) THEN REFL_TAC));;

let ACC_IDX_LT_8 = prove
 (`!m x. MEM x (ACC_IDX m) ==> x < 8`,
  REWRITE_TAC[ACC_IDX] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MEM_FILTER; MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Gather-at-accepted-positions = filter: gathering an 8-element list at the *)
(* positions where a predicate holds equals filtering the list. This is the *)
(* abstract bridge connecting ACC_IDX m (set-bit positions of the mask) to  *)
(* FILTER (<9) (the accepted nibble values): when the mask's bit j is the    *)
(* accept-predicate of nibble j, gathering the eta-value vector at ACC_IDX m *)
(* yields exactly the accepted nibbles' eta values. Combined with            *)
(* PSHUFB_ACCEPTED_PREFIX_NUM and VPMOVSXBD_LANE_EXTRACT this closes the     *)
(* per-sub-iter value chain to REJ_SAMPLE_ETA4_BYTES of the 4-byte block.    *)
let GATHER_FILTERED_IDX_8 = prove
 (`!(P:A->bool) a0 a1 a2 a3 a4 a5 a6 a7.
     MAP (\j. EL j [a0;a1;a2;a3;a4;a5;a6;a7])
         (FILTER (\j. P (EL j [a0;a1;a2;a3;a4;a5;a6;a7])) [0;1;2;3;4;5;6;7]) =
     FILTER P [a0;a1;a2;a3;a4;a5;a6;a7]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FILTER; MAP] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; FILTER]) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* Per-sub-iter value bridge: gathering source bytes g at the accepted       *)
(* positions ACC_IDX m (mask m) equals FILTERing the 8 source bytes by the   *)
(* accept predicate val(.) < 9, PROVIDED the mask bit j agrees with that     *)
(* predicate on byte j. This connects the pshufb-compaction output (indexed  *)
(* by ACC_IDX m) to the functional spec's FILTER over byte values. The       *)
(* hypothesis is discharged at the call site from the vpsubb/vpmovmskb mask  *)
(* construction (bit j of the mask = sign bit of nibble_j - 9 = (nibble<9)). *)
let ETA_GATHER = prove
 (`!(g:int128) (m:byte).
     (!j. j < 8 ==> (bit j m <=> val(word_subword g (8*j,8):byte) < 9))
     ==> MAP (\j:num. word_subword g (8*j,8):byte) (ACC_IDX m) =
         FILTER (\b:byte. val b < 9)
                [word_subword g (0,8); word_subword g (8,8);
                 word_subword g (16,8); word_subword g (24,8);
                 word_subword g (32,8); word_subword g (40,8);
                 word_subword g (48,8); word_subword g (56,8)]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
    MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th) THEN
    MP_TAC(SPEC `6` th) THEN MP_TAC(SPEC `7` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ACC_IDX; FILTER; MAP] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; FILTER]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Generalization of GATHER_FILTERED_IDX_8 post-composed with a value map f:   *)
(* gathering f-of-element at the positions where P holds equals MAP f of the   *)
(* P-FILTERed list. Used at the vmovdqu store where the gathered (compacted)   *)
(* bytes are sign-extended (f = word_sx) and the predicate P selects accepted  *)
(* nibbles. Keeps the value function f and predicate P independent, matching   *)
(* the asm where pshufb gathers the (4-nibble) vector while the mask predicate *)
(* is on the nibble value.                                                     *)
let GATHER_FILTER_MAP_IDX_8 = prove
 (`!(f:byte->A) (P:byte->bool) n0 n1 n2 n3 n4 n5 n6 n7.
     MAP (\j. f (EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte))
         (FILTER (\j. P (EL j [n0;n1;n2;n3;n4;n5;n6;n7])) [0;1;2;3;4;5;6;7]) =
     MAP f (FILTER P [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`P:byte->bool`; `n0:byte`;`n1:byte`;`n2:byte`;`n3:byte`;
                 `n4:byte`;`n5:byte`;`n6:byte`;`n7:byte`] GATHER_FILTERED_IDX_8) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF]);;

(* The full abstract pshufb-compaction-correctness statement: the first     *)
(* popcount(m) = |ACC_IDX m| output bytes of the table-driven VPSHUFB are   *)
(* exactly the source bytes g at the accepted nibble positions ACC_IDX m,   *)
(* in order. This closes item (d): combined with the nibble-extraction and  *)
(* popcount bridges it shows each sub-iter writes the accepted (4-nibble)    *)
(* values compacted to the front. _NUM form maps over num positions.        *)
let PSHUFB_ACCEPTED_PREFIX = prove
 (`!(g:int128) m. m < 256 ==>
     SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (PSHUFB_OUT_LIST g (word m)) =
     MAP (\b:byte. word_subword g (8 * val b,8):byte)
         (MAP word (ACC_IDX(word m:byte)):byte list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PSHUFB_OUT_LIST_AS_MAP] THEN
  REWRITE_TAC[SUB_LIST_0_MAP] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[TABLE_PREFIX_ACC]);;

let PSHUFB_ACCEPTED_PREFIX_NUM = prove
 (`!(g:int128) m. m < 256 ==>
     SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (PSHUFB_OUT_LIST g (word m)) =
     MAP (\j:num. word_subword g (8 * j,8):byte) (ACC_IDX(word m:byte))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PSHUFB_ACCEPTED_PREFIX] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:byte) = x` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ACC_IDX_LT_8) THEN ARITH_TAC);;

(* Helper: the low/high nibble of a byte, taken modulo 256 (the byte-width    *)
(* image after word-construction), is < 16. Used to discharge SUBITER_STORE's *)
(* val < 16 side conditions for the 8 nibbles of a 4-byte block.              *)
let NIB_BOUNDS = prove
 (`!b:byte. val b MOD 16 MOD 256 < 16 /\ (val b DIV 16) MOD 256 < 16`,
  GEN_TAC THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `val(b:byte) DIV 16 < 16` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `val(b:byte) MOD 16` THEN
    REWRITE_TAC[MOD_LE; LE_REFL] THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 16 ==> x < 256`]]);;

(* SUBITER STORE (byte form) — the keystone per-sub-iter value lemma.         *)
(* Given a gather vector g whose byte j is (4 - nibble_j) and a mask m whose  *)
(* bit j is the accept predicate (nibble_j < 9), the first popcount(m) =      *)
(* |ACC_IDX m| bytes of the pshufb compaction equal MAP (4-.) over the        *)
(* accepted nibbles. Composes PSHUFB_ACCEPTED_PREFIX_NUM (gather at ACC_IDX)  *)
(* with GATHER_FILTER_MAP_IDX_8 (gather = filter), discharging the index      *)
(* hypotheses from the two per-lane assumptions. This is instantiated four    *)
(* times (one per sub-iter) in the loop body, with nibbles = the 8 nibbles    *)
(* of the sub-iter's 4-byte block.                                            *)
let SUBITER_STORE = prove
 (`!(g:int128) (m:byte) (n0:byte) n1 n2 n3 n4 n5 n6 n7.
    val n0 < 16 /\ val n1 < 16 /\ val n2 < 16 /\ val n3 < 16 /\
    val n4 < 16 /\ val n5 < 16 /\ val n6 < 16 /\ val n7 < 16 /\
    (!j. j < 8 ==> (bit j m <=> val(EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte) < 9)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
                   word_sub (word 4) (EL j [n0;n1;n2;n3;n4;n5;n6;n7]))
    ==> SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m) =
        MAP (\x:byte. word_sub (word 4) x)
            (FILTER (\x:byte. val x < 9) [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `val(m:byte)`] PSHUFB_ACCEPTED_PREFIX_NUM) THEN
  REWRITE_TAC[WORD_VAL] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ACC_IDX] THEN
  MP_TAC(ISPECL [`\x:byte. word_sub (word 4) x:byte`; `\x:byte. val x < 9`;
                 `n0:byte`;`n1:byte`;`n2:byte`;`n3:byte`;`n4:byte`;`n5:byte`;`n6:byte`;`n7:byte`]
                GATHER_FILTER_MAP_IDX_8) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(!j. MEM j [0;1;2;3;4;5;6;7] ==> (bit j (m:byte) <=> val(EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte) < 9)) /\
    (!j. MEM j [0;1;2;3;4;5;6;7] ==> word_subword (g:int128) (8*j,8):byte =
                   word_sub (word 4) (EL j [n0;n1;n2;n3;n4;n5;n6;n7]))`
   MP_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[MEM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  REWRITE_TAC[FILTER; MAP; MEM] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then
      (MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
       MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th) THEN
       MP_TAC(SPEC `6` th) THEN MP_TAC(SPEC `7` th))
    else NO_TAC)) THEN
  REWRITE_TAC[MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV EL_CONV)) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[]);;

(* For an accepted nibble (n < 9), the byte-width and int16-width forms of the *)
(* eta coefficient (4 - n) sign-extend to the SAME int32. Needed because the   *)
(* asm computes 4-nibble in byte lanes (vpsubb) then vpmovsxbd, while the spec *)
(* uses int16 nibbles; both give word(4-n):int32 for n<9 (no underflow since   *)
(* n<=4 gives 4-n, and 5..8 give the sign-extended negative). 9-way blast.     *)
let SX_SUB4_BYTE_EQ_INT16 = prove
 (`!n. n < 9
       ==> word_sx(word_sub (word 4:byte) (word n:byte)):int32 =
           word_sx(word_sub (word 4:int16) (word n:int16)):int32`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `n < 9 ==> n=0\/n=1\/n=2\/n=3\/n=4\/n=5\/n=6\/n=7\/n=8`)) THEN
  POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_BLAST);;

(* SUBITER STORE (int32 form) — the per-sub-iter store-value lemma keyed to    *)
(* numeric nibble values. Given gather byte j = (4 - v_j) and mask bit j =     *)
(* (v_j < 9), the 8-int32 vpmovsxbd output, truncated to popcount(m) lanes,    *)
(* equals MAP (\v. word_sx(word_sub 4 v)) over the accepted nibbles — i.e. the *)
(* int32 eta coefficients in compacted order. This is exactly the vmovdqu      *)
(* store contribution of one sub-iter; instantiated 4x and composed via        *)
(* REJ_SAMPLE_ETA4_BYTES_16_AS_4 to give the iteration's REJ_SAMPLE step.      *)
let SUBITER_STORE_INT32 = prove
 (`!(g:int128) (m:byte) v0 v1 v2 v3 v4 v5 v6 v7.
    v0<16/\v1<16/\v2<16/\v3<16/\v4<16/\v5<16/\v6<16/\v7<16 /\
    (!j. j < 8 ==> (bit j m <=> EL j [v0;v1;v2;v3;v4;v5;v6;v7] < 9)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
                   word_sub (word 4) (word(EL j [v0;v1;v2;v3;v4;v5;v6;v7]):byte))
    ==> MAP (\b:byte. word_sx b:int32)
            (SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m)) =
        MAP (\v. word_sx(word_sub (word 4:int16) (word v)):int32)
            (FILTER (\v. v < 9) [v0;v1;v2;v3;v4;v5;v6;v7])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `m:byte`;
    `word v0:byte`;`word v1:byte`;`word v2:byte`;`word v3:byte`;
    `word v4:byte`;`word v5:byte`;`word v6:byte`;`word v7:byte`] SUBITER_STORE) THEN
  SUBGOAL_THEN `val(word v0:byte)=v0/\val(word v1:byte)=v1/\val(word v2:byte)=v2/\
                val(word v3:byte)=v3/\val(word v4:byte)=v4/\val(word v5:byte)=v5/\
                val(word v6:byte)=v6/\val(word v7:byte)=v7`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
      `!j. j < 8 ==> val(EL j [word v0;word v1;word v2;word v3;
                               word v4;word v5;word v6;word v7]:byte) =
                     EL j [v0;v1;v2;v3;v4;v5;v6;v7]`
      ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`
        (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
       [ASM_ARITH_TAC; ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        let s=string_of_term(concl th) in
        let h n=let nl=String.length n and hl=String.length s in
          let rec go i=if i+nl>hl then false else if String.sub s i nl=n then true else go(i+1) in go 0 in
        h "bit j")) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        let s=string_of_term(concl th) in
        let h n=let nl=String.length n and hl=String.length s in
          let rec go i=if i+nl>hl then false else if String.sub s i nl=n then true else go(i+1) in go 0 in
        h "word_subword")) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`
        (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
       [ASM_ARITH_TAC; ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF] THEN
  REWRITE_TAC[FILTER; MAP] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]) THEN
  ASM_SIMP_TAC[SX_SUB4_BYTE_EQ_INT16]);;

(* Push a num->int16 word-cast through MAP/FILTER: gathering f over the int16  *)
(* P-filtered (word-cast) list equals gathering (f o word) over the numeric    *)
(* (P o word)-filtered list. Used to convert SUBITER_STORE_INT32's numeric     *)
(* nibble form to the spec's int16 NIBBLES_OF_BYTES form.                      *)
let MAP_FILTER_WORD_NIB = prove
 (`!(f:int16->int32) P (L:num list).
     (!v. MEM v L ==> v < 16)
     ==> MAP f (FILTER P (MAP (word:num->int16) L)) =
         MAP (\v. f(word v)) (FILTER (\v. P(word v)) L)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FILTER] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASM_CASES_TAC `(P:int16->bool)(word h)` THEN
    ASM_REWRITE_TAC[MAP; th]));;

(* For a list of nibble values (< 16), the int16-word accept predicate         *)
(* val(word v) < 9 agrees with the numeric v < 9, so the two FILTERs coincide. *)
let FILTER_VAL_WORD_NIB = prove
 (`!L:num list. (!v. MEM v L ==> v < 16)
     ==> FILTER (\v. val(word v:int16) < 9) L = FILTER (\v. v < 9) L`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word h:int16) = h` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_16] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:num`) THEN REWRITE_TAC[MEM] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FILTER (\v. val(word v:int16) < 9) t = FILTER (\v. v < 9) t`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  REWRITE_TAC[]);;

(* SUBITER STORE (spec form) — the body-ready per-sub-iter store lemma.        *)
(* Given mask m = accept predicate on the 8 nibbles of a 4-byte block          *)
(* [b0;b1;b2;b3] (in NIBBLES_OF_BYTES order: lo,hi per byte) and gather byte   *)
(* j = (4 - nibble_j), the int32 vmovdqu store of one sub-iter (truncated to   *)
(* popcount(m) lanes) equals REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3]. The two      *)
(* hypotheses are discharged in the loop body from the proven nibble-extract   *)
(* and bound/mask (VPSUBB_SIGN_BIT_LT_9, VMOVMSKB) lane lemmas.                 *)
(* Instantiated 4x (one per sub-iter) and composed via                         *)
(* REJ_SAMPLE_ETA4_BYTES_16_AS_4 to give the full iteration's contribution.    *)
let SUBITER_STORE_SPEC = prove
 (`!(g:int128) (m:byte) (b0:byte) b1 b2 b3.
    (!j. j < 8 ==> (bit j m <=>
        EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16] < 9)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
        word_sub (word 4) (word(EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16]):byte))
    ==> MAP (\b:byte. word_sx b:int32)
            (SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m)) =
        REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `m:byte`;
    `val(b0:byte) MOD 16`; `val(b0:byte) DIV 16`; `val(b1:byte) MOD 16`; `val(b1:byte) DIV 16`;
    `val(b2:byte) MOD 16`; `val(b2:byte) DIV 16`; `val(b3:byte) MOD 16`; `val(b3:byte) DIV 16`]
    SUBITER_STORE_INT32) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ; RDIV_LT_EQ] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4] THEN
  SUBGOAL_THEN
   `NIBBLES_OF_BYTES [b0;b1;b2;b3] =
    MAP (word:num->int16)
        [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
         val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16]`
   SUBST1_TAC THENL
   [REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; MAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:int16. word_sx(word_sub (word 4) x):int32`; `\x:int16. val x < 9`;
    `[val(b0:byte) MOD 16; val b0 DIV 16; val(b1:byte) MOD 16; val b1 DIV 16;
      val(b2:byte) MOD 16; val b2 DIV 16; val(b3:byte) MOD 16; val b3 DIV 16]`]
    MAP_FILTER_WORD_NIB) THEN
  SUBGOAL_THEN
   `!v. MEM v [val(b0:byte) MOD 16; val b0 DIV 16; val(b1:byte) MOD 16; val b1 DIV 16;
               val(b2:byte) MOD 16; val b2 DIV 16; val(b3:byte) MOD 16; val b3 DIV 16]
        ==> v < 16`
   ASSUME_TAC THENL
   [REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ; RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FILTER_VAL_WORD_NIB]);;

(* VPMOVSXBD per-lane: the 8 int32 lanes of the sign-extend of an int64 (the *)
(* low 64 bits of the pshufb result) are word_sx of the 8 input bytes. Same  *)
(* structural-isolation recipe as PSHUFB_LANE_EXTRACT (word_sx is a fixed    *)
(* bit-routing, so after isolating each lane WORD_BLAST closes it). Feeds the *)
(* int32 coefficient list: lane k = word_sx(compacted byte k), and with      *)
(* WORD_SUB_4_NIBBLE_INT32_AS_SX the compacted (4 - nibble) byte sign-extends *)
(* to the spec coefficient word_sx(word_sub (word 4) nibble):int32.          *)
let VPMOVSXBD_LANE_EXTRACT = prove
 (`!(x:int64).
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (0,32):int32 = word_sx(word_subword x (0,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (32,32):int32 = word_sx(word_subword x (8,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (64,32):int32 = word_sx(word_subword x (16,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (96,32):int32 = word_sx(word_subword x (24,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (128,32):int32 = word_sx(word_subword x (32,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (160,32):int32 = word_sx(word_subword x (40,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (192,32):int32 = word_sx(word_subword x (48,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (224,32):int32 = word_sx(word_subword x (56,8):byte))`,
  GEN_TAC THEN
  REWRITE_TAC[usimd8; usimd4; usimd2] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128;
           DIMINDEX_256; ARITH] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* ===================================================================== *)
(* STORE-VALUE LANE BRIDGE (cheat-free, 2026-06-11).                     *)
(* These compose the full sub-iter SIMD store value: vpshufb (compacts   *)
(* accepted nibbles via the precomputed table) then vpmovsxbd (sign-     *)
(* extends each byte to int32). STORE_LANE_MATCH gives lane j of the     *)
(* YMM store value = word_sx of the j-th PSHUFB-gathered table byte,     *)
(* feeding STORE_BYTES256_NUM_OF_WORDLIST's lane-match hypothesis.       *)
(* pshuf1 is int256 (vpshufb operates on the full YMM); the store reads  *)
(* only the low 64 bits = low 128-lane = exactly the PSHUFB_OUT_BYTE     *)
(* form (j<8), so the outer word_zx 256<-128 is transparent (WSZ_OK).    *)
(* ===================================================================== *)

(* WSZ_OK: outer word_zx 256<-128 is transparent for low-lane bytes (j<8). *)
let WSZ_OK = prove
 (`!(x:int128) j. j < 8
    ==> word_subword (word_zx x:int256) (8 * j,8):byte = word_subword x (8 * j,8)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`x:int128`; `8*j`; `8`]
    (INST_TYPE [`:256`,`:N`; `:128`,`:M`; `:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_128;DIMINDEX_256] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* VAL4EQ8: structural pshuf1 F uses (4)word index extraction; PSHUFB_OUT_BYTE *)
(* uses (8)word -- same low 4 bits, so the vals agree. *)
let VAL4EQ8 = prove
 (`!i:byte. val(word_subword i (0,4):4 word) = val(word_subword i (0,4):8 word)`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD] THEN
  SIMP_TAC[DIMINDEX_4;DIMINDEX_8;DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* PSHUF1_LOWLANE_BYTE: byte j of the int256 pshuf result (low lane, j<8) *)
(* reduces to PSHUFB_OUT_BYTE. *)
let PSHUF1_LOWLANE_BYTE = prove
 (`!g m j. j < 8
    ==> word_subword
          (word_zx
            (usimd16 (\i. if bit 7 i then word 0:byte
                          else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
          (8 * j,8):byte
        = word_subword g (8 * val (EL j (TABLE_ENTRY m)),8)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WSZ_OK] THEN
  REWRITE_TAC[VAL4EQ8] THEN ASM_SIMP_TAC[PSHUFB_OUT_BYTE]);;

(* VPMOVSXBD_LANE_J: the j<8 quantified form of VPMOVSXBD_LANE_EXTRACT. *)
let VPMOVSXBD_LANE_J = prove
 (`!(x:int64) j. j < 8
    ==> word_subword (usimd8 (\b:byte. word_sx b:int32) x) (32*j,32):int32
        = word_sx (word_subword x (8*j,8):byte)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `j < 8 <=> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VPMOVSXBD_LANE_EXTRACT]);;

(* WZZ_LOW: word_zx(word_zx pshuf1):int64 keeps the low 8 bytes (j<8). *)
let WZZ_LOW = prove
 (`!(p:int256) j. j < 8
    ==> word_subword (word_zx (word_zx p:int128):int64) (8*j,8):byte = word_subword p (8*j,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_zx (p:int256):int128`;`8*j`;`8`]
    (INST_TYPE[`:64`,`:N`;`:128`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  MP_TAC(ISPECL [`p:int256`;`8*j`;`8`]
    (INST_TYPE[`:128`,`:N`;`:256`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
  SUBGOAL_THEN `MIN (8*j+8) 128 <= 256 /\ MIN (8*j+8) 256 <= 128 /\ MIN(8*j+8) 128 <= 64` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> REWRITE_TAC[th2;th1]))]);;

(* ZZCOLLAPSE: strip word_zx 128<-256<-128 on a low-lane byte subword (j<8); used in    *)
(* the sub-iter store gather subgoal (the vpmovsxbd source g = word_zx(word_zx(...))).  *)
let ZZCOLLAPSE = prove
 (`!(X:int128) j. j < 8
    ==> word_subword (word_zx (word_zx X:int256):int128) (8*j,8):byte = word_subword X (8*j,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_zx (X:int128):int256`;`8*j`;`8`]
    (INST_TYPE[`:128`,`:N`;`:256`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  MP_TAC(ISPECL [`X:int128`;`8*j`;`8`]
    (INST_TYPE[`:256`,`:N`;`:128`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_128;DIMINDEX_256] THEN
  SUBGOAL_THEN `MIN (8*j+8) 128 <= 256 /\ MIN (8*j+8) 256 <= 128` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> REWRITE_TAC[th2;th1]))]);;

(* Byte/mask arithmetic lemmas for the sub-iter store maskbit subgoal. *)
let WORD_BYTE_MOD = prove
 (`!n. word(n MOD 256):byte = word n`,
  GEN_TAC THEN SUBGOAL_THEN `256 = 2 EXP dimindex(:8)` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[WORD_MOD_SIZE]]);;

let WORD_ADD_256_BYTE = prove
 (`!a x. word(a + 256 * x):byte = word a`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM WORD_BYTE_MOD] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE `256 * x = x * 256`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let BIT_BYTE_VAL_MOD = prove
 (`!(x:int64) j. j < 8 ==> (bit j (word(val x MOD 256):byte) <=> bit j x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_BYTE_MOD] THEN
  SUBGOAL_THEN `word(val(x:int64)):byte = word_zx x` SUBST1_TAC THENL
   [REWRITE_TAC[word_zx; WORD_VAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[BIT_WORD_ZX; DIMINDEX_8; DIMINDEX_64; ARITH_RULE `j < 8 ==> j < 64`]);;

let LENGTH_ACC_IDX_LE_8 = prove
 (`!m:byte. LENGTH(ACC_IDX m) <= 8`,
  GEN_TAC THEN REWRITE_TAC[ACC_IDX] THEN
  MP_TAC(ISPECL [`\i. bit i (m:byte)`; `[0;1;2;3;4;5;6;7]:num list`] LENGTH_FILTER) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* LENGTH_ACC_IDX_BITSUM: the accept count = sum of the 8 mask bits. Bridges          *)
(* LENGTH(ACC_IDX m) to the bitval-sum used by the popcount / maskbit chain, hence to *)
(* LENGTH(REJ_NIBBLES block) = LENGTH(REJ_SAMPLE block) for the SUBITER_STORE_EXTEND   *)
(* width reconciliation.                                                              *)
let LENGTH_ACC_IDX_BITSUM = prove
 (`!m:byte. LENGTH(ACC_IDX m) =
            bitval(bit 0 m) + bitval(bit 1 m) + bitval(bit 2 m) + bitval(bit 3 m) +
            bitval(bit 4 m) + bitval(bit 5 m) + bitval(bit 6 m) + bitval(bit 7 m)`,
  GEN_TAC THEN REWRITE_TAC[ACC_IDX] THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 0 (m:byte)`;`bit 1 (m:byte)`;`bit 2 (m:byte)`;`bit 3 (m:byte)`;
    `bit 4 (m:byte)`;`bit 5 (m:byte)`;`bit 6 (m:byte)`;`bit 7 (m:byte)`] THEN
  ASM_REWRITE_TAC[FILTER; LENGTH; BITVAL_CLAUSES] THEN ARITH_TAC);;


(* (STORE_LANE_MATCH and its table-dependent deps PSHUF1_BYTE_EQ_OUTLIST /     *)
(*  LENGTH_TABLE_ENTRY are defined later, just after                          *)
(*  LENGTH_MLDSA_REJ_UNIFORM_TABLE, since they need the table length.)        *)

(* VPMOVMSKB on a 64-bit half: pack bit 7 of each of the 8 bytes into  *)
(* a single byte. This is the eta4 analog of VMOVMSKPS_BYTE_EQ from PR  *)
(* #1014. Used to express the result of VPMOVMSKB on the lower lane    *)
(* of the YMM after VPSUBB.                                             *)
let VMOVMSKB_BYTE_EQ_64 = prove
 (`!x:int64. word_of_bits(\i. i < 8 /\ bit(8*i+7) x):byte =
     word(bitval(bit 7 x) + 2 * bitval(bit 15 x) + 4 * bitval(bit 23 x) +
          8 * bitval(bit 31 x) + 16 * bitval(bit 39 x) +
          32 * bitval(bit 47 x) + 64 * bitval(bit 55 x) +
          128 * bitval(bit 63 x))`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_OF_BITS_AS_WORD_ALT; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN
  REWRITE_TAC[IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* MAJOR BRIDGE (concrete byte-mask form, eta4 analog of               *)
(* POPCNT_EQ_LENGTH_FILTER from PR #1014):                              *)
(* The mask byte synthesized from 8 sign-bits of (a_k - 9) — which is   *)
(* what VPMOVMSKB on the VPSUBB result produces — has popcount equal   *)
(* to LENGTH(FILTER (val<9)) over the 8 input nibble-bytes.            *)
let POPCNT_EQ_LENGTH_FILTER_8 = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7:byte.
    val a0 < 16 /\ val a1 < 16 /\ val a2 < 16 /\ val a3 < 16 /\
    val a4 < 16 /\ val a5 < 16 /\ val a6 < 16 /\ val a7 < 16
    ==> word_popcount(word(
         bitval(bit 7 (word_sub a0 (word 9):byte)) +
         2 * bitval(bit 7 (word_sub a1 (word 9):byte)) +
         4 * bitval(bit 7 (word_sub a2 (word 9):byte)) +
         8 * bitval(bit 7 (word_sub a3 (word 9):byte)) +
         16 * bitval(bit 7 (word_sub a4 (word 9):byte)) +
         32 * bitval(bit 7 (word_sub a5 (word 9):byte)) +
         64 * bitval(bit 7 (word_sub a6 (word 9):byte)) +
         128 * bitval(bit 7 (word_sub a7 (word 9):byte))):byte) =
        LENGTH(FILTER (\x:byte. val x < 9) [a0;a1;a2;a3;a4;a5;a6;a7])`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    try let th' = MATCH_MP VPSUBB_SIGN_BIT_LT_9 th in REWRITE_TAC[th']
    with _ -> ASSUME_TAC th)) THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(a0:byte) < 9`; `val(a1:byte) < 9`;
    `val(a2:byte) < 9`; `val(a3:byte) < 9`;
    `val(a4:byte) < 9`; `val(a5:byte) < 9`;
    `val(a6:byte) < 9`; `val(a7:byte) < 9`] THEN
  ASM_REWRITE_TAC[FILTER; bitval; LENGTH] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

(* int32-form per-sub-iter bound: at most 8 int32 values out of 4 bytes. *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_4 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     LENGTH(REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3]:int32 list) <= 8`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MATCH_MP_TAC LENGTH_REJ_NIBBLES_ETA4_4 THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* General length bound: at most 2 nibbles per byte. *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_BOUND = prove
 (`!l:byte list. LENGTH(REJ_SAMPLE_ETA4_BYTES l:int32 list) <= 2 * LENGTH l`,
  GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; LENGTH_REJ_NIBBLES_ETA4]);;

(* Per-sub-iter monotonicity bounds: partial outlen at sub-iter k is at    *)
(* most outlen at end of main iter (= 16-byte chunk). Used to show        *)
(* JA-not-taken for intermediate sub-iters when end-of-iter outlen ≤ 248. *)

let LENGTH_REJ_NIBBLES_ETA4_PREFIX_4 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte)
    (b4:byte) (b5:byte) (b6:byte) (b7:byte)
    (b8:byte) (b9:byte) (b10:byte) (b11:byte)
    (b12:byte) (b13:byte) (b14:byte) (b15:byte).
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list) <=
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7;
                              b8;b9;b10;b11;b12;b13;b14;b15]:int16 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_NIBBLES_ETA4_16_BYTES_SPLIT] THEN ARITH_TAC);;

let LENGTH_REJ_NIBBLES_ETA4_PREFIX_8 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte)
    (b4:byte) (b5:byte) (b6:byte) (b7:byte)
    (b8:byte) (b9:byte) (b10:byte) (b11:byte)
    (b12:byte) (b13:byte) (b14:byte) (b15:byte).
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list) +
     LENGTH(REJ_NIBBLES_ETA4 [b4;b5;b6;b7]:int16 list) <=
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7;
                              b8;b9;b10;b11;b12;b13;b14;b15]:int16 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_NIBBLES_ETA4_16_BYTES_SPLIT] THEN ARITH_TAC);;

let LENGTH_REJ_NIBBLES_ETA4_PREFIX_12 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte)
    (b4:byte) (b5:byte) (b6:byte) (b7:byte)
    (b8:byte) (b9:byte) (b10:byte) (b11:byte)
    (b12:byte) (b13:byte) (b14:byte) (b15:byte).
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list) +
     LENGTH(REJ_NIBBLES_ETA4 [b4;b5;b6;b7]:int16 list) +
     LENGTH(REJ_NIBBLES_ETA4 [b8;b9;b10;b11]:int16 list) <=
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7;
                              b8;b9;b10;b11;b12;b13;b14;b15]:int16 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_NIBBLES_ETA4_16_BYTES_SPLIT] THEN ARITH_TAC);;

(* Generic prefix monotonicity for REJ_SAMPLE_ETA4_BYTES (int32 form). *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_APPEND_LE = prove
 (`!l1 l2:byte list.
     LENGTH(REJ_SAMPLE_ETA4_BYTES l1:int32 list) <=
     LENGTH(REJ_SAMPLE_ETA4_BYTES (APPEND l1 l2):int32 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND; LENGTH_APPEND] THEN ARITH_TAC);;

(* SHR by 8/16/24 commutes with low-byte extraction.                       *)
(* After `shr r8d, 8`, the low 8 bits of r8d are bits 8..15 of original.   *)
(* Used to identify the per-sub-iter mask byte after each SHR.             *)
let WORD_SUBWORD_USHR_LOW8 = prove
 (`(!w:int32. word_subword (word_ushr w 8:int32) (0,8):byte =
              word_subword w (8,8)) /\
   (!w:int32. word_subword (word_ushr w 16:int32) (0,8):byte =
              word_subword w (16,8)) /\
   (!w:int32. word_subword (word_ushr w 24:int32) (0,8):byte =
              word_subword w (24,8))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* AND with 0xF (mask 15) is the byte-level "low nibble" extraction.       *)
(* Used for VPAND ymm0, ymm0, mask where mask = broadcast(0x0F0F0F0F).    *)
let VAL_WORD_AND_15 = prove
 (`!b:byte. val(word_and b (word 15:byte)) = val b MOD 16`,
  GEN_TAC THEN
  SUBGOAL_THEN `(word 15:byte) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ARITH_TAC);;

let VAL_WORD_AND_15_LT_16 = prove
 (`!b:byte. val(word_and b (word 15:byte)) < 16`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_AND_15] THEN ARITH_TAC);;

(* val of a nibble word stays as the nibble value (since nibble < 16 < 256). *)
(* Used after the byte form `word(val b MOD 16):byte` appears in the proof.  *)
let VAL_WORD_NIBBLE = prove
 (`!b:byte. val(word(val b MOD 16):byte) = val b MOD 16 /\
            val(word(val b DIV 16):byte) = val b DIV 16`,
  GEN_TAC THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8; VAL_WORD; DIMINDEX_8] THEN
  STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* word_zx (word n :byte) :int16 = word n when n < 256 (no truncation).   *)
let WORD_ZX_BYTE_TO_INT16 = prove
 (`!n. n < 256 ==> word_zx (word n:byte):int16 = word n`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 65536`]);;

(* LENGTH FILTER (val<9) commutes with MAP word_zx (byte->int16). *)
let LENGTH_FILTER_LT_9_MAP_WORD_ZX = prove
 (`!l:byte list. LENGTH(FILTER (\x:int16. val x < 9) (MAP word_zx l)) =
                  LENGTH(FILTER (\x:byte. val x < 9) l)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FILTER; LENGTH; VAL_WORD_ZX_BYTE_LT_9] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

(* Array_bound element lemma: each element of REJ_SAMPLE_ETA4_BYTES l is     *)
(* in [-4, 4]. This is the per-element form of the CBMC array_bound          *)
(* postcondition.                                                            *)
let REJ_SAMPLE_ETA4_BYTES_COEFF_BOUND = prove
 (`!(l:byte list) c:int32.
     MEM c (REJ_SAMPLE_ETA4_BYTES l)
     ==> --(&4):int <= ival c /\ ival c <= &4`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4; MEM_MAP; MEM_FILTER] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(x:int16) = word(val x)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
    UNDISCH_TAC `val(x:int16) < 9` THEN
    SPEC_TAC(`val(x:int16)`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `n IN {0,1,2,3,4,5,6,7,8}` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC INT_REDUCE_CONV;
    SUBGOAL_THEN `(x:int16) = word(val x)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
    UNDISCH_TAC `val(x:int16) < 9` THEN
    SPEC_TAC(`val(x:int16)`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `n IN {0,1,2,3,4,5,6,7,8}` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC INT_REDUCE_CONV]);;

(* Strengthen-post lemma: an `ensures` whose post implies a stronger post  *)
(* gives an `ensures` for the stronger post.                               *)
(* Used to derive SUBROUTINE_CORRECT (with array_bound) from CORRECT       *)
(* (without array_bound) by showing the array_bound holds at exit.         *)
let ENSURES_STRENGTHEN_POST_X86 = prove
 (`!P (Q:x86state->bool) Q' R.
     ensures x86 P Q' R /\ (!s. Q' s ==> Q s) ==> ensures x86 P Q R`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `s0:x86state` THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL [`x86`;
    `\s':x86state. (Q':x86state->bool) s' /\
                   (R:x86state->x86state->bool) (s0:x86state) s'`;
    `\s':x86state. (Q:x86state->bool) s' /\
                   (R:x86state->x86state->bool) (s0:x86state) s'`]
    EVENTUALLY_MONO)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;

(* SUB_LIST length cap: outlist length <= 256, used for SUBROUTINE_CORRECT  *)
(* `outlen <= 256` postcondition.                                          *)
let LENGTH_SUB_LIST_REJ_SAMPLE_ETA4_BYTES = prove
 (`!(l:byte list).
     LENGTH(SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES l):int32 list) <= 256`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* The exact form needed for SUBROUTINE_CORRECT postcondition:              *)
(*   (!i. i < outlen ==> ival(EL i outlist) < &5 /\ -- &5 < ival(EL i ...))  *)
(* matching PR #1040's aarch64 eta4 SUBROUTINE_CORRECT.                     *)
let REJ_SAMPLE_ETA4_BYTES_EL_BOUND = prove
 (`!(l:byte list) i.
     i < LENGTH(SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES l):int32 list)
     ==> ival(EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES l):int32 list)) < &5 /\
         -- &5 < ival(EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES l):int32 list))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:byte list`;
                 `EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES (l:byte list)):int32 list):int32`]
                REJ_SAMPLE_ETA4_BYTES_COEFF_BOUND) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`REJ_SAMPLE_ETA4_BYTES (l:byte list):int32 list`; `256`]
                  SUB_LIST_TOPSPLIT) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    REWRITE_TAC[MEM_APPEND] THEN DISJ1_TAC THEN
    MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
    INT_ARITH_TAC]);;

(* MAJOR BRIDGE: byte-form LENGTH FILTER for the 8 nibbles extracted from   *)
(* 4 input bytes (after VPMOVZXBW + VPSLLW + VPOR + VPAND) equals          *)
(* LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]).                                 *)
let LENGTH_FILTER_BYTE_NIBBLES_4_BYTES = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     LENGTH(FILTER (\x:byte. val x < 9)
             [word(val b0 MOD 16); word(val b0 DIV 16);
              word(val b1 MOD 16); word(val b1 DIV 16);
              word(val b2 MOD 16); word(val b2 DIV 16);
              word(val b3 MOD 16); word(val b3 DIV 16)]) =
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND] THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(SPEC
   `[word(val(b0:byte) MOD 16); word(val(b0:byte) DIV 16);
     word(val(b1:byte) MOD 16); word(val(b1:byte) DIV 16);
     word(val(b2:byte) MOD 16); word(val(b2:byte) DIV 16);
     word(val(b3:byte) MOD 16); word(val(b3:byte) DIV 16)]:byte list`
   LENGTH_FILTER_LT_9_MAP_WORD_ZX) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MAP] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WORD_ZX_BYTE_TO_INT16 THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* The "ultimate bridge" for sub-iter k: popcount of the mask byte (whose  *)
(* bits are sign bits of (nibble - 9) for the 8 nibbles of 4 input bytes) *)
(* equals LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]). Combines                *)
(* POPCNT_EQ_LENGTH_FILTER_8 + LENGTH_FILTER_BYTE_NIBBLES_4_BYTES into a  *)
(* single MP-able form for the body proof's popcnt step.                  *)
let POPCNT_NIBBLES_4_BYTES_BRIDGE = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     val b0 < 256 /\ val b1 < 256 /\ val b2 < 256 /\ val b3 < 256
     ==> word_popcount(word(
           bitval(bit 7 (word_sub (word(val b0 MOD 16):byte) (word 9))) +
           2 * bitval(bit 7 (word_sub (word(val b0 DIV 16):byte) (word 9))) +
           4 * bitval(bit 7 (word_sub (word(val b1 MOD 16):byte) (word 9))) +
           8 * bitval(bit 7 (word_sub (word(val b1 DIV 16):byte) (word 9))) +
           16 * bitval(bit 7 (word_sub (word(val b2 MOD 16):byte) (word 9))) +
           32 * bitval(bit 7 (word_sub (word(val b2 DIV 16):byte) (word 9))) +
           64 * bitval(bit 7 (word_sub (word(val b3 MOD 16):byte) (word 9))) +
           128 * bitval(bit 7 (word_sub (word(val b3 DIV 16):byte) (word 9)))):byte) =
         LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL
   [`word(val(b0:byte) MOD 16):byte`; `word(val(b0:byte) DIV 16):byte`;
    `word(val(b1:byte) MOD 16):byte`; `word(val(b1:byte) DIV 16):byte`;
    `word(val(b2:byte) MOD 16):byte`; `word(val(b2:byte) DIV 16):byte`;
    `word(val(b3:byte) MOD 16):byte`; `word(val(b3:byte) DIV 16):byte`]
   POPCNT_EQ_LENGTH_FILTER_8) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[VAL_WORD_NIBBLE] THEN
    MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC LENGTH_FILTER_BYTE_NIBBLES_4_BYTES);;

(* ------------------------------------------------------------------------- *)
(* movzbl/popcnt low-byte reduction for the clean loop body.  After the      *)
(* movzbl r8b->r10d the popcnt operand is word_zx layers over                *)
(* word(val mask8 MOD 256) where mask8 = word_zx(word(32-term vpmovmskb       *)
(* bitval sum)); POPCNT_VPMOVMSKB_LOW8 collapses the whole popcnt to the      *)
(* low-8 bitval sum bitval(p0)+..+bitval(p7), which then composes with        *)
(* POPCNT_NIBBLES_4_BYTES_BRIDGE (p k = bit 7 of f1bnd byte k) to give the    *)
(* block accept count.  Supporting: ADD256_MOD, LOW8_LT, MOD_RED.            *)
(* ------------------------------------------------------------------------- *)

let ADD256_MOD = prove
 (`!a b. a < 256 ==> (a + 256 * b) MOD 256 = a`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

let LOW8_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) < 256`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7] THEN ARITH_TAC);;

let MOD_RED = prove
 (`!p:num->bool.
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) MOD 256 =
    bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
    16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)`,
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
     256*bitval(p 16) + 512*bitval(p 17) + 1024*bitval(p 18) + 2048*bitval(p 19) +
     4096*bitval(p 20) + 8192*bitval(p 21) + 16384*bitval(p 22) + 32768*bitval(p 23) +
     65536*bitval(p 24) + 131072*bitval(p 25) + 262144*bitval(p 26) + 524288*bitval(p 27) +
     1048576*bitval(p 28) + 2097152*bitval(p 29) + 4194304*bitval(p 30) + 8388608*bitval(p 31))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ADD256_MOD THEN REWRITE_TAC[LOW8_LT]);;

let POPCNT_VPMOVMSKB_LOW8 = prove
 (`!p:num->bool.
     word_popcount
       (word_zx (word_zx (word_zx
          (word (val (word_zx (word
             (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
              16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
              256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
              4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
              65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
              1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
              16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
              268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)):int32):int64)
            MOD 256):int32):int32):int32):int32) =
     bitval(p 0) + bitval(p 1) + bitval(p 2) + bitval(p 3) +
     bitval(p 4) + bitval(p 5) + bitval(p 6) + bitval(p 7)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `val (word_zx (word
             (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
              16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
              256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
              4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
              65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
              1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
              16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
              268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)):int32):int64)
            MOD 256 =
    bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
    16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)`
   SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; MOD_RED];
    MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
      [0;1;2;3;4;5;6;7] THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV]);;

(* Sub-iter k outlen bound: outlen + sum of popcnts up to sub-iter k <= 248. *)
(* Used to prove JA-not-taken at each sub-iter's `cmp eax, 0xf8`.            *)

(* Unweighted bitval sum = filter-length: the clean-body counter chain leaves R9/RAX
   carrying word_popcount(...) = Σ_{k<8} bitval(bit 7 (f1bnd byte k)) (after the
   POPCNT_VPMOVMSKB low-byte reduction; see the movzbl/popcnt recipe).  With the maskbit
   fact bit 7 (f1bnd byte k) <=> val(nibble_k) < 9, this rewrites the sum to
   LENGTH(FILTER (\x. val x < 9) [nibbles]) = LENGTH(REJ_NIBBLES_ETA4 block) — the block
   accept count = the RAX advance for the mid-guard. *)
(* Collapse the stepped RAX add-nest word_zx(word_add(word_zx(word a))(word_zx(word_zx(word b))))
   to word(a+b) when a+b < 2^32.  After the popcnt+add the clean-body RAX has exactly this
   shape (a = outlen0, b = block accept count); with a+b <= 248 it folds to word(outlen0+count),
   from which the niblen bound + JA_NOT_TAKEN_LE discharges the mid-guard ja. *)
let RAX_NEST_REDUCE = prove
 (`!a b. a + b < 2 EXP 32
     ==> word_zx (word_add (word_zx (word a:int64):int32)
                           (word_zx (word_zx (word b:int32):int64):int32):int32):int64 =
         word(a + b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a < 2 EXP 32 /\ b < 2 EXP 32 /\ a + b < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 64`] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let BITVAL_SUM_8_EQ_LENGTH_FILTER = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7:byte.
     bitval(val a0 < 9) + bitval(val a1 < 9) + bitval(val a2 < 9) + bitval(val a3 < 9) +
     bitval(val a4 < 9) + bitval(val a5 < 9) + bitval(val a6 < 9) + bitval(val a7 < 9) =
     LENGTH(FILTER (\x:byte. val x < 9) [a0;a1;a2;a3;a4;a5;a6;a7])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FILTER; LENGTH] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; BITVAL_CLAUSES]) THEN ARITH_TAC);;

(* ACC_LENGTH_EQ_FILTER: given the per-lane mask<->accept correspondence, the accept   *)
(* count LENGTH(ACC_IDX m) equals LENGTH(FILTER (<9) [the 8 nibble bytes]) = LENGTH     *)
(* (REJ_NIBBLES block) = LENGTH(REJ_SAMPLE block). Width reconciliation for the         *)
(* SUBITER_STORE_EXTEND fold. (Placed after BITVAL_SUM_8_EQ_LENGTH_FILTER which it uses.)*)
let ACC_LENGTH_EQ_FILTER = prove
 (`!(m:byte) (n0:byte) (n1:byte) (n2:byte) (n3:byte) (n4:byte) (n5:byte) (n6:byte) (n7:byte).
     (bit 0 m <=> val n0 < 9) /\ (bit 1 m <=> val n1 < 9) /\ (bit 2 m <=> val n2 < 9) /\
     (bit 3 m <=> val n3 < 9) /\ (bit 4 m <=> val n4 < 9) /\ (bit 5 m <=> val n5 < 9) /\
     (bit 6 m <=> val n6 < 9) /\ (bit 7 m <=> val n7 < 9)
     ==> LENGTH(ACC_IDX m) = LENGTH(FILTER (\x:byte. val x < 9) [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_ACC_IDX_BITSUM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BITVAL_SUM_8_EQ_LENGTH_FILTER]);;

let SUBITER_OUTLEN_BOUND_1 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 12 = 16`]
                     (ISPECL [`inlist:byte list`; `4`; `12`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th; REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND])) THEN
  ASM_ARITH_TAC);;

let SUBITER_OUTLEN_BOUND_2 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 4, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 8 = 16`]
                     (ISPECL [`inlist:byte list`; `8`; `8`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th2; REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND;
                                th1]))) THEN
  ASM_ARITH_TAC);;

let SUBITER_OUTLEN_BOUND_3 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 4, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 8, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `12 + 4 = 16`]
                     (ISPECL [`inlist:byte list`; `12`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 4 = 12`]
                     (ISPECL [`inlist:byte list`; `8`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> DISCH_THEN(fun th3 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th3; th2; th1; REJ_NIBBLES_ETA4_APPEND;
                                LENGTH_APPEND])))) THEN
  ASM_ARITH_TAC);;

(* val(word(16*i):int64) = 16*i when 16 * i <= 256 (i.e. i <= 7).            *)
(* Used to simplify the bytes128 address arithmetic in the body proof.      *)
let VAL_WORD_16_TIMES_I = prove
 (`!(i:num). i <= 7 ==> val(word(16 * i):int64) = 16 * i`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPEC `i:num` LT_REFL) THEN ASM_ARITH_TAC);;

(* val(word(4*n):int64) = 4*n when n <= 248 (output array index).           *)
(* Used to simplify the bytes256 vmovdqu writeback address.                *)
let VAL_WORD_4_TIMES_N = prove
 (`!(n:num). n <= 248 ==> val(word(4 * n):int64) = 4 * n`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* mldsa_rej_uniform_table has 256 entries × 8 bytes per entry.            *)
let LENGTH_MLDSA_REJ_UNIFORM_TABLE = prove
 (`LENGTH (mldsa_rej_uniform_table:byte list) = 2048`,
  REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Table-length-dependent store-value lemmas (cheat-free, 2026-06-11);        *)
(* see the STORE-VALUE LANE BRIDGE block above (WSZ_OK..STORE_LANE_MATCH).    *)
(* These need LENGTH_MLDSA_REJ_UNIFORM_TABLE so they live here.               *)

(* LENGTH_TABLE_ENTRY: a table entry is always 8 bytes (val m < 256 always). *)
let LENGTH_TABLE_ENTRY = prove
 (`!m:byte. LENGTH(TABLE_ENTRY m) = 8`,
  GEN_TAC THEN REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST; LENGTH_MLDSA_REJ_UNIFORM_TABLE] THEN
  MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* PSHUF1_BYTE_EQ_OUTLIST: byte j of the pshuf result = EL j (PSHUFB_OUT_LIST). *)
let PSHUF1_BYTE_EQ_OUTLIST = prove
 (`!g m j. j < 8
    ==> word_subword
          (word_zx
            (usimd16 (\i. if bit 7 i then word 0:byte
                          else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
          (8 * j,8):byte
        = EL j (PSHUFB_OUT_LIST g m)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PSHUF1_LOWLANE_BYTE] THEN
  ASM_SIMP_TAC[PSHUFB_OUT_LIST_AS_MAP; EL_MAP; LENGTH_TABLE_ENTRY]);;

(* STORE_LANE_MATCH: the capstone -- lane j (j<8) of the full vpshufb->vpmovsxbd *)
(* store value equals word_sx of the j-th PSHUFB-gathered table byte. *)
let STORE_LANE_MATCH = prove
 (`!(g:int128) m j. j < 8
    ==> word_subword
          (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx
              (word_zx
                (usimd16 (\i. if bit 7 i then word 0:byte
                              else word_subword g (8 * val (word_subword i (0,4):4 word),8))
                  (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
              :int128):int64))
          (32*j,32):int32
        = word_sx (EL j (PSHUFB_OUT_LIST g m))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VPMOVSXBD_LANE_J] THEN ASM_SIMP_TAC[WZZ_LOW] THEN
  ASM_SIMP_TAC[PSHUF1_BYTE_EQ_OUTLIST]);;

(* LENGTH_PSHUFB_OUT_LIST: the gathered table-byte list is always 8 long. *)
let LENGTH_PSHUFB_OUT_LIST = prove
 (`!g:int128. !m:byte. LENGTH(PSHUFB_OUT_LIST g m) = 8`,
  REWRITE_TAC[PSHUFB_OUT_LIST_AS_MAP; LENGTH_MAP; LENGTH_TABLE_ENTRY]);;

(* STORE_LANE_EQ_REJBLOCK: combines STORE_LANE_MATCH with the SUB_LIST/MAP    *)
(* shape of SUBITER1_VALUE's RHS. For j<k<=8, the YMM store lane j equals the *)
(* j-th element of MAP word_sx (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m)) -- i.e.  *)
(* exactly EL j of the REJ_SAMPLE block (via SUBITER1_VALUE), which is the    *)
(* lane-match hypothesis of STORE_BYTES256_NUM_OF_WORDLIST.                   *)
let STORE_LANE_EQ_REJBLOCK = prove
 (`!(g:int128) m k j. j < k /\ k <= 8
    ==> word_subword
          (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx
              (word_zx
                (usimd16 (\i. if bit 7 i then word 0:byte
                              else word_subword g (8 * val (word_subword i (0,4):4 word),8))
                  (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
              :int128):int64))
          (32*j,32):int32
        = EL j (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j < 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[STORE_LANE_MATCH] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,k)(PSHUFB_OUT_LIST (g:int128) m)) = k` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_MAP] THEN
    ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_PSHUFB_OUT_LIST; ADD_CLAUSES] THEN
    ASM_ARITH_TAC]);;

(* SUBITER_STORE_POSTCOND: the full single-store value bridge. Given the     *)
(* bytes256 read of the destination equals the vpshufb->vpmovsxbd store      *)
(* value (PSHUFB pipeline form) and k<=8, the 4k stored bytes = the          *)
(* num_of_wordlist of the k-element accepted block. Lane-match is discharged *)
(* internally via STORE_LANE_EQ_REJBLOCK.                                    *)
let SUBITER_STORE_POSTCOND = prove
 (`!A s (g:int128) m k.
     k <= 8 /\
     read (memory :> bytes256 A) s =
       (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
                else word_subword g (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64))
     ==> read (memory :> bytes(A, 4 * k)) s =
         num_of_wordlist (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:int64`;
    `usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
                else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64)`;
    `MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST (g:int128) m))`;
    `k:num`; `s:x86state`] STORE_BYTES256_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STORE_LANE_EQ_REJBLOCK THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* SUBITER_STORE_EXTEND: fold a freshly-stored int32 block into the running  *)
(* output prefix (both are int32 lists; the new block sits at res+4*|prefix|).*)
let SUBITER_STORE_EXTEND = prove
 (`!res s (prefix:int32 list) (block:int32 list).
     read (memory :> bytes(res, 4 * LENGTH prefix)) s = num_of_wordlist prefix /\
     read (memory :> bytes(word_add res (word (4 * LENGTH prefix)), 4 * LENGTH block)) s
       = num_of_wordlist block
     ==> read (memory :> bytes(res, 4 * LENGTH prefix + 4 * LENGTH block)) s
         = num_of_wordlist (APPEND prefix block)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s:x86state`;
                 `prefix:int32 list`; `block:int32 list`;
                 `4 * LENGTH(prefix:int32 list)`; `4 * LENGTH(block:int32 list)`]
        (INST_TYPE [`:32`,`:N`] BYTES_EQ_NUM_OF_WORDLIST_APPEND)) THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[]);;

(* Byte-digitization of the 16-byte chunk the SIMD loop consumes per       *)
(* iteration. The `vpmovzxbw (rsi,rcx)` load (rcx = 16*i, rsi = buf) reads  *)
(* bytes128 at buf + 16*i; this lemma identifies the 16 byte-subwords of    *)
(* that 128-bit value with SUB_LIST(16*i, 16) inlist, given the buffer      *)
(* contract read(memory :> bytes(buf,buflen)) = num_of_wordlist inlist.     *)
(* x86 128-bit analogue of aarch64_utils' SUB_LIST_8_BYTES_FROM_INT64.      *)
let SUB_LIST_16_BYTES_FROM_INT128 = prove
 (`!buf:int64 buflen inlist i s.
    16 * (i + 1) <= buflen /\
    LENGTH (inlist:byte list) = buflen /\
    read (memory :> bytes (buf, buflen)) s = num_of_wordlist inlist
    ==> SUB_LIST (16 * i, 16) inlist =
        [word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (0,8):byte;
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (8,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (16,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (24,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (32,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (40,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (48,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (56,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (64,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (72,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (80,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (88,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (96,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (104,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (112,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (120,8)]`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
    `loaded_d = read (memory :> bytes128 (word_add buf (word (16 * i)))) s` THEN
  CONV_TAC SYM_CONV THEN
  REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
    `\x. x DIV 2 EXP (8 * 16 * i) MOD 2 EXP (8 * 16)`) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (buflen - 16 * i) 16 = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`word_add buf (word (16 * i)):int64`; `read memory s`]
    (INST_TYPE[`:128`,`:N`] VAL_READ_WBYTES)) THEN
  REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES; GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* VPMOVZXBW byte-extraction: byte 2k of the int256 result = byte k of    *)
(* the int128 input (byte 2k+1 = 0). Used to extract individual nibble    *)
(* bytes from the simulator's `read YMM0 sN` after VPMOVZXBW.             *)
let VPMOVZXBW_BYTE_EXTRACT = prove
 (`(!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (0,8):byte
      = word_subword q (0,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (16,8):byte
      = word_subword q (8,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (32,8):byte
      = word_subword q (16,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (48,8):byte
      = word_subword q (24,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (64,8):byte
      = word_subword q (32,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (80,8):byte
      = word_subword q (40,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (96,8):byte
      = word_subword q (48,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (112,8):byte
      = word_subword q (56,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (128,8):byte
      = word_subword q (64,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (144,8):byte
      = word_subword q (72,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (160,8):byte
      = word_subword q (80,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (176,8):byte
      = word_subword q (88,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (192,8):byte
      = word_subword q (96,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (208,8):byte
      = word_subword q (104,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (224,8):byte
      = word_subword q (112,8)) /\
   (!q:int128.
      word_subword (usimd16 (\b:byte. (word_zx b):int16) q:int256) (240,8):byte
      = word_subword q (120,8))`,
  REWRITE_TAC[usimd16; usimd8; usimd4; usimd2; DIMINDEX_8; DIMINDEX_16;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* int16-lane extraction from VPMOVZXBW result: each 16-bit lane k of the    *)
(* 256-bit output equals word_zx of byte k of the 128-bit input.              *)
let VPMOVZXBW_LANE_EXTRACT = prove
 (`!q:int128.
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (0,16):int16
    = word_zx (word_subword q (0,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (16,16):int16
    = word_zx (word_subword q (8,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (32,16):int16
    = word_zx (word_subword q (16,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (48,16):int16
    = word_zx (word_subword q (24,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (64,16):int16
    = word_zx (word_subword q (32,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (80,16):int16
    = word_zx (word_subword q (40,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (96,16):int16
    = word_zx (word_subword q (48,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (112,16):int16
    = word_zx (word_subword q (56,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (128,16):int16
    = word_zx (word_subword q (64,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (144,16):int16
    = word_zx (word_subword q (72,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (160,16):int16
    = word_zx (word_subword q (80,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (176,16):int16
    = word_zx (word_subword q (88,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (192,16):int16
    = word_zx (word_subword q (96,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (208,16):int16
    = word_zx (word_subword q (104,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (224,16):int16
    = word_zx (word_subword q (112,8):byte)) /\
   (word_subword (usimd16 (\b:byte. word_zx b:int16) q:int256) (240,16):int16
    = word_zx (word_subword q (120,8):byte))`,
  REWRITE_TAC[usimd16; usimd8; usimd4; usimd2; DIMINDEX_8; DIMINDEX_16;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* The VPSLLW + VPOR + VPAND chain on a zero-extended byte b produces an     *)
(* int16 whose low byte is val(b) MOD 16 and whose high byte is val(b) DIV 16.*)
(* This is the core SIMD-output simplification for sub-iter 1 nibble extract. *)
let VPSLLW_VPOR_VPAND_LOW_BYTE = prove
 (`!b:byte. word_subword
        (word_and
          (word_or (word_zx b:int16) (word_shl (word_zx b:int16) 4))
          (word 3855:int16))
        (0,8):byte = word(val b MOD 16)`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_AND;
              BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD;
              DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `i < 16` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `!j. j < 4
         ==> (val(b:byte) MOD 16) DIV 2 EXP j =
             (val b DIV 2 EXP j) MOD 2 EXP (4 - j)`
   (LABEL_TAC "MODDIV") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `j + 4 - j = 4` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  REWRITE_TAC[BIT_VAL] THEN ASM_CASES_TAC `i < 4` THENL
   [REMOVE_THEN "MODDIV" (fun th ->
       ASSUME_TAC(MATCH_MP th (ASSUME `i < 4`))) THEN
    ASM_REWRITE_TAC[ODD_MOD_POW2;
                    ARITH_RULE `~(4 - i = 0) <=> i < 4`] THEN
    SUBGOAL_THEN `~(4 <= i)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ODD (3855 DIV 2 EXP i)` ASSUME_TAC THENL
     [SUBGOAL_THEN `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(val(b:byte) MOD 16) DIV 2 EXP i = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 4` THEN
      REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN CONJ_TAC THENL
       [ARITH_TAC; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[ODD] THEN
    SUBGOAL_THEN `~ODD (3855 DIV 2 EXP i)` (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `i = 4 \/ i = 5 \/ i = 6 \/ i = 7` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let VPSLLW_VPOR_VPAND_HIGH_BYTE = prove
 (`!b:byte. word_subword
        (word_and
          (word_or (word_zx b:int16) (word_shl (word_zx b:int16) 4))
          (word 3855:int16))
        (8,8):byte = word(val b DIV 16)`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_AND;
              BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD;
              DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bit (8 + i) (b:byte) <=> F` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b:byte`; `8 + i`] BIT_TRIVIAL) THEN
    REWRITE_TAC[DIMINDEX_8] THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `8 + i < 16 /\ 4 <= 8 + i /\ (8 + i) - 4 < 16`
    STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(8 + i) - 4 = i + 4` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[BIT_VAL] THEN
  SUBGOAL_THEN `val(b:byte) DIV 2 EXP (i + 4) = val b DIV 16 DIV 2 EXP i`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXP_ADD] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 4` THENL
   [SUBGOAL_THEN `ODD (3855 DIV 2 EXP (8 + i))` (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    SUBGOAL_THEN `val(b:byte) DIV 16 DIV 2 EXP i = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 4` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
        ARITH_TAC;
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      REWRITE_TAC[ODD]]]);;

(* Fused form of the int16 chain output: an int16 lane after VPMOVZXBW +     *)
(* VPSLLW + VPOR + VPAND has high byte = val(b) DIV 16 (high nibble) and low *)
(* byte = val(b) MOD 16 (low nibble) — i.e. nibble-pair-as-int16 layout.     *)
let VPSLLW_VPOR_VPAND_INT16_NIBBLES = prove
 (`!b:byte. word_and (word_or (word_zx b:int16) (word_shl (word_zx b:int16) 4))
                     (word 3855:int16) =
            word_join (word(val b DIV 16):byte) (word(val b MOD 16):byte):int16`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_SHL;
              BIT_WORD_ZX; BIT_WORD; BIT_WORD_JOIN; DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[BIT_VAL] THEN
  SUBGOAL_THEN
    `!j. j < 4
         ==> (val(b:byte) MOD 16) DIV 2 EXP j =
             (val b DIV 2 EXP j) MOD 2 EXP (4 - j)`
   (LABEL_TAC "MODDIV") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `j + 4 - j = 4` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 8` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `i < 4` THENL
     [REMOVE_THEN "MODDIV" (fun th ->
         ASSUME_TAC(MATCH_MP th (ASSUME `i < 4`))) THEN
      ASM_REWRITE_TAC[ODD_MOD_POW2;
                      ARITH_RULE `~(4 - i = 0) <=> i < 4`] THEN
      SUBGOAL_THEN `~(4 <= i)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `ODD (3855 DIV 2 EXP i)` ASSUME_TAC THENL
       [SUBGOAL_THEN `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(val(b:byte) MOD 16) DIV 2 EXP i = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN
        MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 4` THEN
        REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN CONJ_TAC THENL
         [ARITH_TAC; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[ODD] THEN
      SUBGOAL_THEN `~ODD (3855 DIV 2 EXP i)` (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `i = 4 \/ i = 5 \/ i = 6 \/ i = 7` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
    SUBGOAL_THEN `val(b:byte) DIV 2 EXP i = 0` ASSUME_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 8` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
        ARITH_TAC;
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ODD] THEN
    SUBGOAL_THEN `4 <= i /\ i - 4 < 16 /\ i - 8 < 8` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(b:byte) DIV 2 EXP (i - 4) = val b DIV 16 DIV 2 EXP (i - 8)`
      SUBST1_TAC THENL
     [REWRITE_TAC[DIV_DIV] THEN
      SUBGOAL_THEN `16 * 2 EXP (i - 8) = 2 EXP (i - 4)` SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; GSYM EXP_ADD] THEN
        AP_TERM_TAC THEN ASM_ARITH_TAC;
        REFL_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `i < 12` THENL
     [SUBGOAL_THEN `ODD (3855 DIV 2 EXP i)` (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `i = 8 \/ i = 9 \/ i = 10 \/ i = 11` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      SUBGOAL_THEN `val(b:byte) DIV 16 DIV 2 EXP (i-8) = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN
        MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 4` THEN
        CONJ_TAC THENL
         [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          ARITH_TAC;
          REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[ODD] THEN
      SUBGOAL_THEN `~ODD (3855 DIV 2 EXP i)` (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `i = 12 \/ i = 13 \/ i = 14 \/ i = 15` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]]);;

(* Form bridge: the simulator's vpmovzxbw output (a flat word_join of 16     *)
(* word_zx(word_subword q (8k,8)) lanes, after the stepper composes the       *)
(* nested usimd subwords) equals usimd16 word_zx q. As a rewrite it folds the *)
(* stepped YMM0 (load) back into usimd16 form so F0NIB_BYTES applies. Defined *)
(* via the usimd-unfold + WORD_SUBWORD_SUBWORD-compose conversion (GSYM), so  *)
(* its LHS is exactly the flat form the simulator emits.                      *)
let VPMOVZXBW_FLAT = GSYM
  ((REWRITE_CONV[usimd16;usimd8;usimd4;usimd2] THENC ONCE_DEPTH_CONV BETA_CONV THENC
    SIMP_CONV[WORD_SUBWORD_SUBWORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64; DIMINDEX_128; DIMINDEX_256; ARITH] THENC
    NUM_REDUCE_CONV)
   `usimd16 (\b:byte. word_zx b:int16) (q:int128):int256`);;

(* Byte structure of the full nibble-extraction SIMD chain (vpmovzxbw +
   vpsllw $4 + vpor + vpand mask) against the CONCRETE 0x0F0F0F0F broadcast
   constant carried in the loop invariant (YMM2). Output byte 2j = low
   nibble of input byte j (= val MOD 16), byte 2j+1 = high nibble (val DIV
   16) -- matching NIBBLES_OF_BYTES order. This is what reduces the vpand
   result (opaque without the YMM2 invariant) to nibble form in CLEAN_BODY. *)
let F0NIB_BYTES = prove
 (`!q:int128.
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (0,8):byte =
     word(val(word_subword q (0,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (8,8):byte =
     word(val(word_subword q (0,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (16,8):byte =
     word(val(word_subword q (8,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (24,8):byte =
     word(val(word_subword q (8,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (32,8):byte =
     word(val(word_subword q (16,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (40,8):byte =
     word(val(word_subword q (16,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (48,8):byte =
     word(val(word_subword q (24,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (56,8):byte =
     word(val(word_subword q (24,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (64,8):byte =
     word(val(word_subword q (32,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (72,8):byte =
     word(val(word_subword q (32,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (80,8):byte =
     word(val(word_subword q (40,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (88,8):byte =
     word(val(word_subword q (40,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (96,8):byte =
     word(val(word_subword q (48,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (104,8):byte =
     word(val(word_subword q (48,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (112,8):byte =
     word(val(word_subword q (56,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (120,8):byte =
     word(val(word_subword q (56,8):byte) DIV 16))`,
  GEN_TAC THEN
  REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* word_subword of a byte at (0,8) is the identity -- closes the residual    *)
(* byte-of-byte wrapper left after the join-subword lane extraction.         *)
let WORD_SUBWORD_BYTE_ID = prove
 (`!x:byte. word_subword x (0,8):byte = x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Byte structure of the eta vpsubb (vpsubb f0, eta, f0 = eta - f0nib) against *)
(* the CONCRETE eta=0x04040404 broadcast (YMM3 in the loop invariant): output  *)
(* byte j = word_sub (word 4) (input byte j). Composed with F0NIB_BYTES this   *)
(* gives the gather vector f0sub byte j = word_sub (word 4) (word nibble_j),   *)
(* exactly SUBITER_STORE_SPEC's gather hypothesis. The join-subword lane       *)
(* extraction (WORD_SUBWORD_JOIN_LOWER/UPPER) avoids WORD_BLAST blowup on the  *)
(* 256-bit join; WORD_RED_CONV reduces the eta constant's lanes to word 4.     *)
let F0SUB_BYTES = prove
 (`!f:int256.
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (0,8):byte =
     word_sub (word 4) (word_subword (f:int256) (0,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (8,8):byte =
     word_sub (word 4) (word_subword (f:int256) (8,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (16,8):byte =
     word_sub (word 4) (word_subword (f:int256) (16,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (24,8):byte =
     word_sub (word 4) (word_subword (f:int256) (24,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (32,8):byte =
     word_sub (word 4) (word_subword (f:int256) (32,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (40,8):byte =
     word_sub (word 4) (word_subword (f:int256) (40,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (48,8):byte =
     word_sub (word 4) (word_subword (f:int256) (48,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (56,8):byte =
     word_sub (word 4) (word_subword (f:int256) (56,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (64,8):byte =
     word_sub (word 4) (word_subword (f:int256) (64,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (72,8):byte =
     word_sub (word 4) (word_subword (f:int256) (72,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (80,8):byte =
     word_sub (word 4) (word_subword (f:int256) (80,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (88,8):byte =
     word_sub (word 4) (word_subword (f:int256) (88,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (96,8):byte =
     word_sub (word 4) (word_subword (f:int256) (96,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (104,8):byte =
     word_sub (word 4) (word_subword (f:int256) (104,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (112,8):byte =
     word_sub (word 4) (word_subword (f:int256) (112,8):byte)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256) (f:int256)) (120,8):byte =
     word_sub (word 4) (word_subword (f:int256) (120,8):byte))`,
  GEN_TAC THEN
  REWRITE_TAC[simd2;simd16;simd8;simd4;simd2] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128;
           DIMINDEX_256; ARITH] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  SIMP_TAC[WORD_SUBWORD_SUBWORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
           DIMINDEX_64; DIMINDEX_128; DIMINDEX_256; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_SUBWORD_BYTE_ID]);;

let SUBITER_GATHER_NIB = prove
 (`!q:int128.
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (0,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (0,8):byte) MOD 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (8,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (0,8):byte) DIV 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (16,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (8,8):byte) MOD 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (24,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (8,8):byte) DIV 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (32,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (16,8):byte) MOD 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (40,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (16,8):byte) DIV 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (48,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (24,8):byte) MOD 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (56,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (24,8):byte) DIV 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (64,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (32,8):byte) MOD 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (72,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (32,8):byte) DIV 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (80,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (40,8):byte) MOD 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (88,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (40,8):byte) DIV 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (96,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (48,8):byte) MOD 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (104,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (48,8):byte) DIV 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (112,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (56,8):byte) MOD 16))) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))) (120,8):byte =
     word_sub (word 4) (word(val(word_subword (q:int128) (56,8):byte) DIV 16)))`,
  GEN_TAC THEN REWRITE_TAC[F0SUB_BYTES; F0NIB_BYTES]);;

(* Byte structure of the bound vpsubb (vpsubb bound, f0, f1 = f0nib - bound)   *)
(* against the CONCRETE bound=0x09090909 broadcast (YMM4): output byte j =      *)
(* word_sub (input byte j) (word 9). With F0NIB_BYTES (nibbles < 16) and        *)
(* VPSUBB_SIGN_BIT_LT_9, bit 7 of this byte <=> nibble_j < 9 -- the input to    *)
(* vpmovmskb, giving SUBITER_STORE_SPEC's mask hypothesis.                      *)
let F1BND_BYTES = prove
 (`!f:int256.
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (0,8):byte =
     word_sub (word_subword (f:int256) (0,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (8,8):byte =
     word_sub (word_subword (f:int256) (8,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (16,8):byte =
     word_sub (word_subword (f:int256) (16,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (24,8):byte =
     word_sub (word_subword (f:int256) (24,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (32,8):byte =
     word_sub (word_subword (f:int256) (32,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (40,8):byte =
     word_sub (word_subword (f:int256) (40,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (48,8):byte =
     word_sub (word_subword (f:int256) (48,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (56,8):byte =
     word_sub (word_subword (f:int256) (56,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (64,8):byte =
     word_sub (word_subword (f:int256) (64,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (72,8):byte =
     word_sub (word_subword (f:int256) (72,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (80,8):byte =
     word_sub (word_subword (f:int256) (80,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (88,8):byte =
     word_sub (word_subword (f:int256) (88,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (96,8):byte =
     word_sub (word_subword (f:int256) (96,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (104,8):byte =
     word_sub (word_subword (f:int256) (104,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (112,8):byte =
     word_sub (word_subword (f:int256) (112,8):byte) (word 9)) /\
    (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (f:int256) (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (120,8):byte =
     word_sub (word_subword (f:int256) (120,8):byte) (word 9))`,
  GEN_TAC THEN
  REWRITE_TAC[simd2;simd16;simd8;simd4;simd2] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128;
           DIMINDEX_256; ARITH] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  SIMP_TAC[WORD_SUBWORD_SUBWORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
           DIMINDEX_64; DIMINDEX_128; DIMINDEX_256; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_SUBWORD_BYTE_ID]);;

let SIGN_NIB = prove
 (`!n. n < 16 ==> (bit 7 (word_sub (word n:byte) (word 9)) <=> n < 9)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:byte) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `word n:byte` VPSUBB_SIGN_BIT_LT_9) THEN ASM_REWRITE_TAC[]);;

let SUBITER_MASK_NIB = prove
 (`!q:int128.
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (0,8):byte) <=>
     val(word_subword (q:int128) (0,8):byte) MOD 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (8,8):byte) <=>
     val(word_subword (q:int128) (0,8):byte) DIV 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (16,8):byte) <=>
     val(word_subword (q:int128) (8,8):byte) MOD 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (24,8):byte) <=>
     val(word_subword (q:int128) (8,8):byte) DIV 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (32,8):byte) <=>
     val(word_subword (q:int128) (16,8):byte) MOD 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (40,8):byte) <=>
     val(word_subword (q:int128) (16,8):byte) DIV 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (48,8):byte) <=>
     val(word_subword (q:int128) (24,8):byte) MOD 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (56,8):byte) <=>
     val(word_subword (q:int128) (24,8):byte) DIV 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (64,8):byte) <=>
     val(word_subword (q:int128) (32,8):byte) MOD 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (72,8):byte) <=>
     val(word_subword (q:int128) (32,8):byte) DIV 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (80,8):byte) <=>
     val(word_subword (q:int128) (40,8):byte) MOD 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (88,8):byte) <=>
     val(word_subword (q:int128) (40,8):byte) DIV 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (96,8):byte) <=>
     val(word_subword (q:int128) (48,8):byte) MOD 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (104,8):byte) <=>
     val(word_subword (q:int128) (48,8):byte) DIV 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (112,8):byte) <=>
     val(word_subword (q:int128) (56,8):byte) MOD 16 < 9) /\
    (bit 7 (word_subword (simd2 (\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2)
        (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256)
                   (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) (q:int128):int256):int256))
          (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256))
        (word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256)) (120,8):byte) <=>
     val(word_subword (q:int128) (56,8):byte) DIV 16 < 9)`,
  GEN_TAC THEN REWRITE_TAC[F1BND_BYTES; F0NIB_BYTES] THEN
  MAP_EVERY (fun bk -> ASSUME_TAC(REWRITE_RULE[DIMINDEX_8]
     (ISPEC (subst[mk_small_numeral bk,`B:num`] `word_subword (q:int128) (B,8):byte`) VAL_BOUND)))
    [0;8;16;24;32;40;48;56] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC SIGN_NIB THEN ASM_ARITH_TAC);;

(* Bit j (j<8) of the byte synthesised by the low half of VPMOVMSKB (the 8     *)
(* low sign-bits packed as bitval sum) equals the j-th predicate. With         *)
(* F1BND_BYTES + VPSUBB_SIGN_BIT_LT_9 this gives mask bit j <=> nibble_j < 9 -- *)
(* the movzbl-extracted sub-iter mask, completing SUBITER_STORE_SPEC's mask     *)
(* hypothesis.                                                                  *)
let MASK_LOW_BIT = prove
 (`!(p:num->bool) j. j < 8
     ==> (bit j (word(bitval(p 0) + 2 * bitval(p 1) + 4 * bitval(p 2) + 8 * bitval(p 3) +
                       16 * bitval(p 4) + 32 * bitval(p 5) + 64 * bitval(p 6) +
                       128 * bitval(p 7)):byte) <=> p j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `j < 8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
  POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  MAP_EVERY BOOL_CASES_TAC [`(p:num->bool) 0`;`(p:num->bool) 1`;`(p:num->bool) 2`;`(p:num->bool) 3`;
                            `(p:num->bool) 4`;`(p:num->bool) 5`;`(p:num->bool) 6`;`(p:num->bool) 7`] THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV BIT_WORD_CONV) THEN REWRITE_TAC[]);;

(* Mask-accept composition: the vpmovmskb low byte, built from the sign bits   *)
(* of the bound vpsubb (nibble - 9), has bit j <=> nibble_j < 9 when each       *)
(* nibble < 16. Composes MASK_LOW_BIT (bit extraction) + VPSUBB_SIGN_BIT_LT_9.  *)
(* This is exactly SUBITER_STORE_SPEC's mask hypothesis (with n = the block's   *)
(* 8 nibbles).                                                                  *)
let MASK_ACCEPT = prove
 (`!(n:num->byte) j. j < 8 /\ (!k. k < 8 ==> val(n k) < 16)
     ==> ((bit j (word(bitval(bit 7 (word_sub (n 0) (word 9):byte)) +
                      2 * bitval(bit 7 (word_sub (n 1) (word 9):byte)) +
                      4 * bitval(bit 7 (word_sub (n 2) (word 9):byte)) +
                      8 * bitval(bit 7 (word_sub (n 3) (word 9):byte)) +
                      16 * bitval(bit 7 (word_sub (n 4) (word 9):byte)) +
                      32 * bitval(bit 7 (word_sub (n 5) (word 9):byte)) +
                      64 * bitval(bit 7 (word_sub (n 6) (word 9):byte)) +
                      128 * bitval(bit 7 (word_sub (n 7) (word 9):byte))):byte))
          <=> val(n j) < 9)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\k. bit 7 (word_sub ((n:num->byte) k) (word 9):byte)`; `j:num`] MASK_LOW_BIT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VPSUBB_SIGN_BIT_LT_9 THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* SUBITER1_VALUE: the per-sub-iter store-value capstone.  For the standard   *)
(* SIMD chain on a free 128-bit chunk `q` (vpmovzxbw / vpsllw$4 / vpor /      *)
(* vpand 0x0F mask / vpsubb eta / vpsubb bound / vpmovmskb / vextracti128$0 / *)
(* vpshufb / vpmovsxbd), the 8-int32 vmovdqu store truncated to the accepted  *)
(* count equals REJ_SAMPLE_ETA4_BYTES of the four chunk bytes.  The gather    *)
(* source `g` is `word_subword f0sub (0,128):int128` (the vextracti128 $0 low *)
(* lane), reconciling SUBITER_STORE_SPEC's int128 `g` with the int256 chain.  *)
(* Both SUBITER_STORE_SPEC hypotheses discharge automatically: the mask via   *)
(* SUBITER_MASK_NIB + MASK_LOW_BIT, the gather via WORD_SUBWORD_SUBWORD        *)
(* (low-lane byte = full-chain byte for j<8) + SUBITER_GATHER_NIB.            *)
(* The statement is built programmatically from the proven NIB lemmas so it   *)
(* tracks their exact simulator forms.                                        *)
let SUBITER1_VALUE =
  let f0sub = rand(rator(lhand(hd(conjuncts(snd(strip_forall(concl SUBITER_GATHER_NIB))))))) in
  let g_term = mk_comb(mk_comb(`word_subword:int256->num#num->int128`, f0sub), `(0,128)`) in
  let f1b = rand(rator(rand(lhand(hd(conjuncts(snd(strip_forall(concl SUBITER_MASK_NIB)))))))) in
  let bk k = vsubst [f1b,`FB:int256`; mk_small_numeral(8*k),`P:num`]
               `bitval(bit 7 (word_subword (FB:int256) (P,8):byte))` in
  let summ = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
    (List.map2 (fun c k -> if c=1 then bk k else mk_binop `( * ):num->num->num` (mk_small_numeral c) (bk k))
       [1;2;4;8;16;32;64;128] (0--7)) in
  let m_term = mk_comb(`word:num->byte`, summ) in
  let sis = SPECL [g_term; m_term;
                   `word_subword (q:int128) (0,8):byte`; `word_subword (q:int128) (8,8):byte`;
                   `word_subword (q:int128) (16,8):byte`; `word_subword (q:int128) (24,8):byte`]
              SUBITER_STORE_SPEC in
  let stmt = mk_forall(`q:int128`, rand(concl sis)) in
  let plist = `\k:num. EL k [val (word_subword (q:int128) (0,8):byte) MOD 16 < 9;
                           val (word_subword (q:int128) (0,8):byte) DIV 16 < 9;
                           val (word_subword (q:int128) (8,8):byte) MOD 16 < 9;
                           val (word_subword (q:int128) (8,8):byte) DIV 16 < 9;
                           val (word_subword (q:int128) (16,8):byte) MOD 16 < 9;
                           val (word_subword (q:int128) (16,8):byte) DIV 16 < 9;
                           val (word_subword (q:int128) (24,8):byte) MOD 16 < 9;
                           val (word_subword (q:int128) (24,8):byte) DIV 16 < 9]` in
  prove(stmt,
    GEN_TAC THEN MATCH_MP_TAC SUBITER_STORE_SPEC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
        (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SUBITER_MASK_NIB] THEN
      W(fun (asl,w) ->
         let n = rand(rator(lhand w)) in
         MP_TAC(SPECL [plist; n] MASK_LOW_BIT) THEN
         CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
         ANTS_TAC THENL [ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC]);
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
        (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[WORD_SUBWORD_SUBWORD; DIMINDEX_128; DIMINDEX_256; ARITH] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
      REWRITE_TAC[SUBITER_GATHER_NIB]]);;

(* ------------------------------------------------------------------------- *)
(* HIGH-HALF byte lemmas (output bytes 16..31 of the 32-byte SIMD vectors,    *)
(* i.e. bit offsets 128..248).  Sub-iters 3 and 4 read the high 128-bit lane  *)
(* of f0sub/f1bnd (via `vextracti128 $1`), which holds the nibbles of input   *)
(* chunk bytes 8..15.  The low-half lemmas (F0NIB_BYTES / F0SUB_BYTES /        *)
(* F1BND_BYTES) only cover bytes 0..15; these are the verbatim analogues for  *)
(* bytes 16..31, proved by the identical recipes.                            *)
let F0NIB_BYTES_HI =
  let chain = rand(rator(lhand(hd(conjuncts(snd(strip_forall(concl F0NIB_BYTES))))))) in
  let mk_cj bi =
    let off = 128 + 8*bi in
    let qbyte = 8 + bi/2 in
    let hi = (bi mod 2 = 1) in
    let lhs = mk_comb(mk_comb(`word_subword:int256->num#num->byte`, chain),
                      mk_pair(mk_small_numeral off, `8`)) in
    let v = mk_comb(`val:byte->num`, mk_comb(mk_comb(`word_subword:int128->num#num->byte`,`q:int128`),
                      mk_pair(mk_small_numeral(8*qbyte), `8`))) in
    let nib = if hi then mk_binop `DIV` v `16` else mk_binop `MOD` v `16` in
    mk_eq(lhs, mk_comb(`word:num->byte`, nib)) in
  prove(mk_forall(`q:int128`, end_itlist (curry mk_conj) (map mk_cj (0--15))),
    GEN_TAC THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;
                DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

let F0SUB_BYTES_HI =
  let eta_c = rand(rator(rand(rator(lhand(hd(conjuncts(snd(strip_forall(concl F0SUB_BYTES))))))))) in
  let simd2sub = `\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2` in
  let mk_cj off =
    let lhs = mk_comb(mk_comb(`word_subword:int256->num#num->byte`,
                list_mk_comb(`simd2:(int128->int128->int128)->int256->int256->int256`,
                             [simd2sub; eta_c; `f:int256`])),
                mk_pair(mk_small_numeral off, `8`)) in
    let rhs = mk_comb(mk_comb(`word_sub:byte->byte->byte`,`word 4:byte`),
                mk_comb(mk_comb(`word_subword:int256->num#num->byte`,`f:int256`),
                        mk_pair(mk_small_numeral off,`8`))) in
    mk_eq(lhs,rhs) in
  prove(mk_forall(`f:int256`, end_itlist (curry mk_conj) (map (fun i -> mk_cj (128+8*i)) (0--15))),
    GEN_TAC THEN REWRITE_TAC[simd2;simd16;simd8;simd4] THEN
    SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
             DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;
             DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_SUBWORD_BYTE_ID]);;

let F1BND_BYTES_HI =
  let bnd_c = rand(rand(rator(lhand(hd(conjuncts(snd(strip_forall(concl F1BND_BYTES)))))))) in
  let simd2sub = `\w1:int128 w2:int128. simd16 (\a:byte b:byte. word_sub a b) w1 w2` in
  let mk_cj off =
    let lhs = mk_comb(mk_comb(`word_subword:int256->num#num->byte`,
                list_mk_comb(`simd2:(int128->int128->int128)->int256->int256->int256`,
                             [simd2sub; `f:int256`; bnd_c])),
                mk_pair(mk_small_numeral off, `8`)) in
    let rhs = mk_comb(mk_comb(`word_sub:byte->byte->byte`,
                mk_comb(mk_comb(`word_subword:int256->num#num->byte`,`f:int256`),
                        mk_pair(mk_small_numeral off,`8`))),
                `word 9:byte`) in
    mk_eq(lhs,rhs) in
  prove(mk_forall(`f:int256`, end_itlist (curry mk_conj) (map (fun i -> mk_cj (128+8*i)) (0--15))),
    GEN_TAC THEN REWRITE_TAC[simd2;simd16;simd8;simd4] THEN
    SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
             DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;
             DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_SUBWORD_BYTE_ID]);;

(* High-lane gather/mask NIB composites (analogues of SUBITER_GATHER_NIB /     *)
(* SUBITER_MASK_NIB for f0sub/f1bnd bytes 16..31 = chunk bytes 8..15).         *)
let SUBITER_GATHER_NIB_HI =
  let f0sub_full = rand(rator(lhand(hd(conjuncts(snd(strip_forall(concl SUBITER_GATHER_NIB))))))) in
  let mk_g_cj bi =
    let off = 128 + 8*bi in
    let qbyte = 8 + bi/2 in
    let hi = (bi mod 2 = 1) in
    let lhs = mk_comb(mk_comb(`word_subword:int256->num#num->byte`, f0sub_full),
                      mk_pair(mk_small_numeral off,`8`)) in
    let v = mk_comb(`val:byte->num`, mk_comb(mk_comb(`word_subword:int128->num#num->byte`,`q:int128`),
                      mk_pair(mk_small_numeral(8*qbyte),`8`))) in
    let nib = if hi then mk_binop `DIV` v `16` else mk_binop `MOD` v `16` in
    mk_eq(lhs, mk_comb(mk_comb(`word_sub:byte->byte->byte`,`word 4:byte`),
                       mk_comb(`word:num->byte`,nib))) in
  prove(mk_forall(`q:int128`, end_itlist (curry mk_conj) (map mk_g_cj (0--15))),
    GEN_TAC THEN REWRITE_TAC[F0SUB_BYTES_HI; F0NIB_BYTES_HI]);;

let SUBITER_MASK_NIB_HI =
  let f1bnd_full = rand(rator(rand(lhand(hd(conjuncts(snd(strip_forall(concl SUBITER_MASK_NIB)))))))) in
  let mk_m_cj bi =
    let off = 128 + 8*bi in
    let qbyte = 8 + bi/2 in
    let hi = (bi mod 2 = 1) in
    let lhs = vsubst [f1bnd_full,`FB:int256`; mk_small_numeral off,`P:num`]
                `bit 7 (word_subword (FB:int256) (P,8):byte)` in
    let v = mk_comb(`val:byte->num`, mk_comb(mk_comb(`word_subword:int128->num#num->byte`,`q:int128`),
                      mk_pair(mk_small_numeral(8*qbyte),`8`))) in
    let nib = if hi then mk_binop `DIV` v `16` else mk_binop `MOD` v `16` in
    mk_eq(lhs, mk_binop `(<):num->num->bool` nib `9`) in
  prove(mk_forall(`q:int128`, end_itlist (curry mk_conj) (map mk_m_cj (0--15))),
    GEN_TAC THEN REWRITE_TAC[F1BND_BYTES_HI; F0NIB_BYTES_HI] THEN
    MAP_EVERY (fun bk -> ASSUME_TAC(REWRITE_RULE[DIMINDEX_8]
       (ISPEC (subst[mk_small_numeral bk,`B:num`] `word_subword (q:int128) (B,8):byte`) VAL_BOUND)))
      [64;72;80;88;96;104;112;120] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC SIGN_NIB THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Per-sub-iter store-value lemmas for sub-iters 2, 3, 4 (sub-iter 1 is       *)
(* SUBITER1_VALUE above).  Sub-iter k stores REJ_SAMPLE_ETA4_BYTES of chunk   *)
(* bytes [4(k-1)..4(k-1)+3].  The gather source g is the appropriate 128-bit  *)
(* lane of f0sub:                                                             *)
(*   k=2: word_subword f0sub (64,128)   (vpsrldq $8 of the low lane)          *)
(*   k=3: word_subword f0sub (128,128)  (vextracti128 $1, high lane)          *)
(*   k=4: word_subword f0sub (192,128)  (vpsrldq $8 of the high lane)         *)
(* k=2 uses the low-half NIB lemmas, k=3/4 the HI ones.                       *)
let SUBITER2_VALUE, SUBITER3_VALUE, SUBITER4_VALUE =
  let mk_subiter k lanebase gnib mnib =
    let qb i = 8*(4*(k-1)+i) in
    let f0sub = rand(rator(lhand(hd(conjuncts(snd(strip_forall(concl SUBITER_GATHER_NIB))))))) in
    let g_term = mk_comb(mk_comb(`word_subword:int256->num#num->int128`, f0sub),
                         mk_pair(mk_small_numeral lanebase, `128`)) in
    let f1b = rand(rator(rand(lhand(hd(conjuncts(snd(strip_forall(concl SUBITER_MASK_NIB)))))))) in
    let bk j = vsubst [f1b,`FB:int256`; mk_small_numeral(lanebase+8*j),`P:num`]
                 `bitval(bit 7 (word_subword (FB:int256) (P,8):byte))` in
    let summ = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (List.map2 (fun c j -> if c=1 then bk j else mk_binop `( * ):num->num->num` (mk_small_numeral c) (bk j))
         [1;2;4;8;16;32;64;128] (0--7)) in
    let m_term = mk_comb(`word:num->byte`, summ) in
    let byteterm i = mk_comb(mk_comb(`word_subword:int128->num#num->byte`,`q:int128`),
                             mk_pair(mk_small_numeral(qb i), `8`)) in
    let sis = SPECL [g_term; m_term; byteterm 0; byteterm 1; byteterm 2; byteterm 3] SUBITER_STORE_SPEC in
    let stmt = mk_forall(`q:int128`, rand(concl sis)) in
    let pl i hi =
      let v = mk_comb(`val:byte->num`, byteterm i) in
      let nib = if hi then mk_binop `DIV` v `16` else mk_binop `MOD` v `16` in
      mk_binop `(<):num->num->bool` nib `9` in
    let plist = mk_abs(`k:num`,
      let lst = end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b)
         (List.concat (map (fun i -> [pl i false; pl i true]) (0--3)) @ [`[]:(bool)list`]) in
      mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`), lst)) in
    prove(stmt,
      GEN_TAC THEN MATCH_MP_TAC SUBITER_STORE_SPEC THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
          (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[mnib] THEN
        W(fun (asl,w) ->
           let n = rand(rator(lhand w)) in
           MP_TAC(SPECL [plist; n] MASK_LOW_BIT) THEN
           CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
           ANTS_TAC THENL [ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC]);
        REPEAT STRIP_TAC THEN
        FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
          (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SIMP_TAC[WORD_SUBWORD_SUBWORD; DIMINDEX_128; DIMINDEX_256; ARITH] THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
        REWRITE_TAC[gnib]]) in
  mk_subiter 2 64  SUBITER_GATHER_NIB    SUBITER_MASK_NIB,
  mk_subiter 3 128 SUBITER_GATHER_NIB_HI SUBITER_MASK_NIB_HI,
  mk_subiter 4 192 SUBITER_GATHER_NIB_HI SUBITER_MASK_NIB_HI;;

(* Address simplification: the simulator's `word_add buf (word(1 * val ...))`*)
(* form arising from VPMOVZXBW addressing reduces to `word_add buf (word(16*i))` *)
(* given i <= 7 (which holds because 16 * i <= 256).                         *)
let WORD_ADD_BUF_VAL_SIMP = prove
 (`!(buf:int64) (i:num). i <= 7
     ==> word_add buf (word(1 * val(word(16*i):int64))):int64 =
         word_add buf (word(16*i))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MULT_CLAUSES] THEN
  MATCH_MP_TAC VAL_WORD_16_TIMES_I THEN ASM_REWRITE_TAC[]);;

(* Nibble normalization: a byte with val < 16 has trivial MOD/DIV behavior. *)
let VAL_BYTE_LT_16_MOD = prove
 (`!a:byte. val a < 16 ==> val a MOD 16 = val a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

let VAL_BYTE_LT_16_DIV = prove
 (`!a:byte. val a < 16 ==> val a DIV 16 = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN ASM_REWRITE_TAC[]);;

(* word(val a):byte = a — used to undo `word(val a)` form back to a. *)
let WORD_VAL_BYTE = prove
 (`!a:byte. val a < 16 ==> word(val a):byte = a`,
  REPEAT STRIP_TAC THEN MATCH_ACCEPT_TAC WORD_VAL);;


(* Final equation: outlen at i+1 = outlen at i + sum of 4 sub-iter contribs.*)
let SUBITER_OUTLEN_STEP_4 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list) =
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 4, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 8, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 12, 4) inlist):int16 list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `12 + 4 = 16`]
                     (ISPECL [`inlist:byte list`; `12`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 4 = 12`]
                     (ISPECL [`inlist:byte list`; `8`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> DISCH_THEN(fun th3 ->
    REWRITE_TAC[th3; th2; th1; REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND]))) THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Mid-guard / partial-outlen lemmas for CLEAN_BODY's sub-iter `ja` checks.   *)
(* After sub-iter 1 (which appends the first 4-byte block), the running       *)
(* count RAX = outlen0 + |accepted nibbles in block 0| = niblen(16i+4); the   *)
(* mid-iter `ja $248` must NOT fire on a clean iteration (i+1 < N), i.e. that  *)
(* partial count is <= 248 because it is a prefix of niblen(16(i+1)) <= 248.   *)

(* The partial outlen after sub-iter 1: outlen0 + block-0 accept count equals  *)
(* the full int32-list length of the prefix SUB_LIST(0,16i+4).                 *)
let SUBITER1_PARTIAL_OUTLEN = prove
 (`!inlist i.
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist):int32 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i,4) inlist):int16 list) =
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  SUBGOAL_THEN `SUB_LIST(0,16*i+4) (inlist:byte list) =
                APPEND (SUB_LIST(0,16*i) inlist) (SUB_LIST(16*i,4) inlist)`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`inlist:byte list`; `16*i`; `4`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND]]);;

(* Generic per-sub-iter outlen advance: appending the 4-byte block at offset    *)
(* 16i+d extends the running int32 outlist length by that block's accept count.  *)
(* (SUBITER1_PARTIAL_OUTLEN is the d=0 instance.) Used to thread RAX = niblen of  *)
(* the running prefix across the 4 sub-iters.                                    *)
let SUBITER_PARTIAL_OUTLEN_STEP = prove
 (`!inlist i d.
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+d) inlist):int32 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+d,4) inlist):int16 list) =
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,(16*i+d)+4) inlist):int32 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(ISPECL [`inlist:byte list`; `16*i+d`; `4`; `0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND]);;

(* Generic partial-prefix bound: for any d <= 16, the nibble-length of the     *)
(* prefix SUB_LIST(0,16i+d) is <= niblen(16(i+1)), hence <= 248 on clean iters.*)
let SUBITER_PARTIAL_OUTLEN_LE = prove
 (`!inlist i d.
     d <= 16 /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*i+d) inlist):int16 list) <= 248`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LE_TRANS `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(i+1)) inlist):int16 list)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`inlist:byte list`; `16*i+d`; `16*(i+1)`] NIBLEN_PREFIX_MONO) THEN
  ANTS_TAC THENL [UNDISCH_TAC `d <= 16` THEN ARITH_TAC; REWRITE_TAC[]]);;

(* The int32-list (RAX) form of the partial-outlen bound, for the mid-guard.   *)
let SUBITER1_PARTIAL_OUTLEN_LE = prove
 (`!inlist i.
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`; `4`] SUBITER_PARTIAL_OUTLEN_LE) THEN
  ASM_REWRITE_TAC[ARITH]);;

(* List-decomposition lemmas: a 4-byte list is [b0;b1;b2;b3] for some bytes,*)
(* a 16-byte list similarly. Used to introduce the named bytes b_k for the *)
(* per-sub-iter input chunk SUB_LIST(16*i, 16) inlist.                     *)
let LIST_4_DECOMP = prove
 (`!l:byte list. LENGTH l = 4
     ==> ?b0 b1 b2 b3:byte. l = [b0;b1;b2;b3]`,
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; LENGTH_EQ_CONS;
              LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let LIST_16_DECOMP = prove
 (`!l:byte list. LENGTH l = 16
     ==> ?b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15:byte.
         l = [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]`,
  REWRITE_TAC[ARITH_RULE
   `16 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))))))))))`;
   LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

(* Bound corollary: popcnt of mask byte (sub-iter k contribution) is <= 8 *)
let POPCNT_NIBBLES_4_BYTES_LE_8 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     val b0 < 256 /\ val b1 < 256 /\ val b2 < 256 /\ val b3 < 256
     ==> word_popcount(word(
           bitval(bit 7 (word_sub (word(val b0 MOD 16):byte) (word 9))) +
           2 * bitval(bit 7 (word_sub (word(val b0 DIV 16):byte) (word 9))) +
           4 * bitval(bit 7 (word_sub (word(val b1 MOD 16):byte) (word 9))) +
           8 * bitval(bit 7 (word_sub (word(val b1 DIV 16):byte) (word 9))) +
           16 * bitval(bit 7 (word_sub (word(val b2 MOD 16):byte) (word 9))) +
           32 * bitval(bit 7 (word_sub (word(val b2 DIV 16):byte) (word 9))) +
           64 * bitval(bit 7 (word_sub (word(val b3 MOD 16):byte) (word 9))) +
           128 * bitval(bit 7 (word_sub (word(val b3 DIV 16):byte) (word 9)))):byte) <= 8`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b0:byte`;`b1:byte`;`b2:byte`;`b3:byte`]
              POPCNT_NIBBLES_4_BYTES_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LENGTH_REJ_NIBBLES_ETA4_4 THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* bit-of-subword lifts: for a byte extracted from an int32, the byte's    *)
(* bit i is bit (i+offset) of the original int32 (for offsets 0/8/16/24). *)
let BIT_SUBWORD_BYTE_OF_INT32 = prove
 (`(!w:int32 i. i < 8 ==> (bit i (word_subword w (0,8):byte) <=> bit i w)) /\
   (!w:int32 i. i < 8
                ==> (bit i (word_subword w (8,8):byte) <=> bit (i+8) w)) /\
   (!w:int32 i. i < 8
                ==> (bit i (word_subword w (16,8):byte) <=> bit (i+16) w)) /\
   (!w:int32 i. i < 8
                ==> (bit i (word_subword w (24,8):byte) <=> bit (i+24) w))`,
  REWRITE_TAC[BIT_WORD_SUBWORD; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `0 + i = i`; ARITH_RULE `8 + i = i + 8`;
              ARITH_RULE `16 + i = i + 16`; ARITH_RULE `24 + i = i + 24`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* SCALAR TAIL HELPER: REJ_SAMPLE_ETA4_BYTES on a single byte = at most 2 *)
(* int32s, computed from low nibble (b MOD 16) and high nibble (b DIV 16).*)
(* The scalar tail loop processes one byte per iteration this way.        *)
let REJ_SAMPLE_ETA4_BYTES_1 = prove
 (`!b:byte.
     REJ_SAMPLE_ETA4_BYTES [b] =
     APPEND
      (if val b MOD 16 < 9
       then [word_sx(word_sub (word 4:int16) (word(val b MOD 16))):int32]
       else [])
      (if val b DIV 16 < 9
       then [word_sx(word_sub (word 4:int16) (word(val b DIV 16))):int32]
       else [])`,
  GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4;
              NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; FILTER; MAP] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `val(b:byte) MOD 16 MOD 65536 = val b MOD 16 /\
    val(b:byte) DIV 16 MOD 65536 = val b DIV 16`
   (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]);;

(* int32-level nibble extraction lemmas for the scalar tail.                *)
(* `and r10d, 15` extracts the low nibble; `shr r11d, 4` then `and r11d, 15` *)
(* extracts the high nibble. These bridge to the spec's val(b) MOD/DIV 16.    *)
let VAL_WORD_AND_15_INT32 = prove
 (`!b:byte. val(word_and (word_zx b:int32) (word 15:int32)) = val b MOD 16`,
  GEN_TAC THEN
  SUBGOAL_THEN `(word 15:int32) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOD_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let VAL_WORD_USHR_4_AND_15_INT32 = prove
 (`!b:byte. val(word_and (word_ushr (word_zx b:int32) 4) (word 15:int32)) =
            val b DIV 16`,
  GEN_TAC THEN
  SUBGOAL_THEN `(word 15:int32) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR; VAL_WORD_ZX_GEN;
              DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`val(b:byte)`; `16`] DIV_LT) THEN
  ASM_ARITH_TAC);;

(* The scalar tail computes `4 - nibble` as an int32 directly via `mov r11d 4; *)
(* sub r11d, r10d`, while the spec uses `word_sx (word_sub (word 4:int16)     *)
(* (word n)):int32`. For accepted nibbles (n < 9), these forms are equal.     *)
let WORD_SUB_4_NIBBLE_INT32_AS_SX = prove
 (`!n. n < 9
       ==> word_sub (word 4:int32) (word n):int32 =
           word_sx(word_sub (word 4:int16) (word n):int16):int32`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/
                n = 6 \/ n = 7 \/ n = 8` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST);;

(* Length bound on REJ_SAMPLE_ETA4_BYTES restricted to a SUB_LIST prefix.    *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_SUB_LIST_BOUND = prove
 (`!(inlist:byte list) k.
     k <= LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k) inlist):int32 list) <= 2 * k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(0, k) (inlist:byte list):byte list`
              LENGTH_REJ_SAMPLE_ETA4_BYTES_BOUND) THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST_0]);;

(* Prefix lemma: REJ_SAMPLE_ETA4_BYTES has a prefix structure on SUB_LIST *)
let REJ_SAMPLE_ETA4_SUB_LIST_PREFIX = prove
 (`!k (l:byte list).
     k <= LENGTH l
     ==> ?rest:int32 list.
         APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,k) l)) rest =
         REJ_SAMPLE_ETA4_BYTES l`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `REJ_SAMPLE_ETA4_BYTES (SUB_LIST(k, LENGTH l - k) l):int32 list` THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; GSYM MAP_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; GSYM FILTER_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NIBBLES_OF_BYTES_APPEND] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`] SUB_LIST_TOPSPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REFL_TAC);;

(* Final-state composition: when scalar tail terminates with outlen = 256,  *)
(* the partial sample list IS the SUB_LIST(0,256) of the full input's       *)
(* REJ_SAMPLE_ETA4_BYTES. Used in subgoal 3 final step to match the         *)
(* SUBROUTINE_CORRECT postcondition.                                        *)
let SUB_LIST_256_FROM_PARTIAL_REJ = prove
 (`!(inlist:byte list) k.
     k <= LENGTH inlist /\
     LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST(0, k) inlist):int32 list) = 256
     ==> SUB_LIST(0, 256)(REJ_SAMPLE_ETA4_BYTES inlist :int32 list) =
         REJ_SAMPLE_ETA4_BYTES (SUB_LIST(0, k) inlist)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `inlist:byte list`] REJ_SAMPLE_ETA4_SUB_LIST_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ext:int32 list` (SUBST1_TAC o SYM)) THEN
  UNDISCH_TAC `LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,k) (inlist:byte list))
                       :int32 list) = 256` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[SUB_LIST_APPEND_LEFT; LE_REFL] THEN
  REWRITE_TAC[SUB_LIST_LENGTH]);;

(* Reconstruct byte from its low and high nibbles. *)
let WORD_BYTE_FROM_NIBBLES = prove
 (`!(b:byte). word(val b MOD 16 + 16 * (val b DIV 16)):byte = b`,
  GEN_TAC THEN
  SUBGOAL_THEN `val b MOD 16 + 16 * (val(b:byte) DIV 16) = val b` SUBST1_TAC THENL
   [MP_TAC(SPECL [`val(b:byte)`; `16`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    MATCH_ACCEPT_TAC WORD_VAL]);;

(* Both nibbles are < 16 (always true for byte). *)
let VAL_BYTE_NIBBLES_LT_16 = prove
 (`(!(b:byte). val b DIV 16 < 16) /\ (!(b:byte). val b MOD 16 < 16)`,
  CONJ_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    STRIP_TAC THEN MP_TAC(SPECL [`val(b:byte)`; `16`] DIV_LT) THEN ASM_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]]);;

(* Sum of nibbles bound. *)
let NIBBLE_SUM_LT_256 = prove
 (`!a:num b:num. a < 16 /\ b < 16 ==> a + 16 * b < 256`,
  ARITH_TAC);;

(* DIVISION decomposition: val b = val b MOD 16 + 16 * (val b DIV 16). *)
let VAL_BYTE_DIVISION = prove
 (`!(b:byte). val b = val b MOD 16 + 16 * (val b DIV 16)`,
  GEN_TAC THEN MP_TAC(SPECL [`val(b:byte)`; `16`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

(* If val b < 16 then both nibbles simplify. *)
let VAL_BYTE_LT_16_NIBBLES = prove
 (`!(b:byte). val b < 16 ==> val b MOD 16 = val b /\ val b DIV 16 = 0`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT; DIV_LT]);;

(* LENGTH of REJ_SAMPLE_ETA4_BYTES on a single byte is at most 2. *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_1_LE_2 = prove
 (`!(b:byte). LENGTH(REJ_SAMPLE_ETA4_BYTES [b]:int32 list) <= 2`,
  GEN_TAC THEN REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[LENGTH; APPEND]) THEN ARITH_TAC);;

(* val of EL k of byte list is always < 256. *)
let VAL_EL_BYTE_LT_256 = prove
 (`!(inlist:byte list) (k:num). val(EL k inlist:byte) < 256`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `EL k (inlist:byte list):byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* SUB_LIST(0, 256) of length-256 list is identity. *)
let SUB_LIST_256_EQ = prove
 (`!(l:int32 list). LENGTH l = 256 ==> SUB_LIST(0, 256) l = l`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `LENGTH (l:int32 list) = 256` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC SUB_LIST_LENGTH);;

(* val(word(val b MOD/DIV 16)):byte = val b MOD/DIV 16 — nibble normalization. *)
let VAL_WORD_NIBBLE_LO_BYTE = prove
 (`!(b:byte). val(word(val b MOD 16):byte) = val b MOD 16`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`val(b:byte)`; `16`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

let VAL_WORD_NIBBLE_HI_BYTE = prove
 (`!(b:byte). val(word(val b DIV 16):byte) = val b DIV 16`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`val(b:byte)`; `16`] DIV_LT) THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  ARITH_TAC);;

let VAL_WORD_NIBBLE_LO_INT16 = prove
 (`!(b:byte). val(word(val b MOD 16):int16) = val b MOD 16`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`val(b:byte)`; `16`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

let VAL_WORD_NIBBLE_HI_INT16 = prove
 (`!(b:byte). val(word(val b DIV 16):int16) = val b DIV 16`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`val(b:byte)`; `16`] DIV_LT) THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  ARITH_TAC);;

(* val(word a) = a when a fits. *)
let VAL_WORD_LT_INT32 = prove
 (`!a:num. a < 2 EXP 32 ==> val(word a:int32) = a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let VAL_WORD_LT_INT64 = prove
 (`!a:num. a < 2 EXP 64 ==> val(word a:int64) = a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* word_add of two words equals word of sum, when no overflow. *)
let WORD_ADD_WORDS_INT32 = prove
 (`!a:num b:num. a + b < 2 EXP 32 ==> word_add (word a:int32) (word b) = word(a + b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 32 = a /\ b MOD 2 EXP 32 = b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* ival of word_sx (word_sub (word 4:int16) (word n)):int32 = 4 - n. Used  *)
(* directly in array_bound proof for accepted nibbles.                      *)
let IVAL_WORD_SX_SUB_4_NIBBLE_INT32 = prove
 (`!n. n < 9 ==> ival(word_sx(word_sub (word 4:int16) (word n):int16):int32) = &4 - &n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o
    MATCH_MP (ARITH_RULE
      `n < 9 ==> n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/
                 n = 5 \/ n = 6 \/ n = 7 \/ n = 8`)) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_ARITH);;

(* The array_bound corollary: for accepted nibbles, the int32 coefficient   *)
(* satisfies -5 < ival < 5. Used directly in REJ_SAMPLE_ETA4_BYTES_EL_BOUND.*)
let IVAL_WORD_SX_SUB_4_NIBBLE_BOUND = prove
 (`!n. n < 9
       ==> ival(word_sx(word_sub (word 4:int16) (word n):int16):int32) < &5 /\
           -- &5 < ival(word_sx(word_sub (word 4:int16) (word n):int16):int32)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `n:num` IVAL_WORD_SX_SUB_4_NIBBLE_INT32) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* ival of word_sub (word 4:int16) (word n) = &4 - &n for accepted nibbles. *)
(* This is the int16-form coefficient bound that aligns with REJ_SAMPLE_ETA4 *)
(* spec output (int16 coeff = 4 - nibble in [-4,4]).                        *)
let IVAL_WORD_SUB_4_NIBBLE_INT16 = prove
 (`!n. n < 9 ==> ival(word_sub (word 4:int16) (word n):int16) = &4 - &n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/
                n = 5 \/ n = 6 \/ n = 7 \/ n = 8` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_ARITH);;

(* word_subword extract of low byte of bitsum (8 boolean bits packed).    *)
(* Used to take low 8 bits of vpmovmskb 32-bit result.                     *)
(* word_subword extract of low byte from a small int32. Used when reading  *)
(* a byte from memory and converting back to byte type.                     *)
let WORD_SUBWORD_BYTE_LT_256 = prove
 (`!a:num. a < 256 ==> word_subword (word a:int32) (0,8):byte = word a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MATCH_MP_TAC(MESON[] `a = b ==> a MOD c = b MOD c`) THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let WORD_SUBWORD_BITSUM_BYTE = prove
 (`!(b0:bool) (b1:bool) (b2:bool) (b3:bool) (b4:bool) (b5:bool) (b6:bool) (b7:bool).
     word_subword
       (word(bitval b0 + 2 * bitval b1 + 4 * bitval b2 + 8 * bitval b3 +
             16 * bitval b4 + 32 * bitval b5 + 64 * bitval b6 + 128 * bitval b7):int32)
       (0,8):byte =
     word(bitval b0 + 2 * bitval b1 + 4 * bitval b2 + 8 * bitval b3 +
          16 * bitval b4 + 32 * bitval b5 + 64 * bitval b6 + 128 * bitval b7)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_BYTE_LT_256 THEN
  MP_TAC(ISPEC `b0:bool` BITVAL_BOUND) THEN
  MP_TAC(ISPEC `b1:bool` BITVAL_BOUND) THEN
  MP_TAC(ISPEC `b2:bool` BITVAL_BOUND) THEN
  MP_TAC(ISPEC `b3:bool` BITVAL_BOUND) THEN
  MP_TAC(ISPEC `b4:bool` BITVAL_BOUND) THEN
  MP_TAC(ISPEC `b5:bool` BITVAL_BOUND) THEN
  MP_TAC(ISPEC `b6:bool` BITVAL_BOUND) THEN
  MP_TAC(ISPEC `b7:bool` BITVAL_BOUND) THEN ARITH_TAC);;

(* int256 -> int128 truncation via word_subword (0,128) is word_zx.        *)
let WORD_SUBWORD_INT256_LOW128 = prove
 (`!(x:int256). word_subword x (0,128):int128 = word_zx x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_WORD_ZX_INT128_INT256 = prove
 (`!(x:int256). word_subword (word_zx x:int128) (0,128):int128 = word_subword x (0,128)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* word_subword extracts the byte from a zero-extended byte-int32/int64.   *)
let WORD_SUBWORD_WORD_ZX_BYTE_INT32 = prove
 (`!(b:byte). word_subword (word_zx b:int32) (0,8):byte = b`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_WORD_ZX_BYTE_INT64 = prove
 (`!(b:byte). word_subword (word_zx b:int64) (0,8):byte = b`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* NIBBLES_OF_BYTES on 4 bytes gives 8 int16 nibbles in alternating order. *)
let NIBBLES_OF_BYTES_4 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     NIBBLES_OF_BYTES [b0;b1;b2;b3]:int16 list =
     [word(val b0 MOD 16); word(val b0 DIV 16);
      word(val b1 MOD 16); word(val b1 DIV 16);
      word(val b2 MOD 16); word(val b2 DIV 16);
      word(val b3 MOD 16); word(val b3 DIV 16)]`,
  REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND]);;

let LENGTH_NIBBLES_OF_BYTES_4 = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     LENGTH (NIBBLES_OF_BYTES [b0;b1;b2;b3]:int16 list) = 8`,
  REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; LENGTH] THEN ARITH_TAC);;

(* Sign-bit bridges for VPSUBB byte-9: directional case applications. *)
let VPSUBB_SIGN_BIT_LT_9_TRUE = prove
 (`!(b:byte). val b < 9 ==> bit 7 (word_sub b (word 9):byte)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `b:byte` VPSUBB_SIGN_BIT_LT_9) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let VPSUBB_SIGN_BIT_LT_9_FALSE = prove
 (`!(b:byte). val b < 16 /\ ~(val b < 9) ==> ~bit 7 (word_sub b (word 9):byte)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `b:byte` VPSUBB_SIGN_BIT_LT_9) THEN
  ASM_REWRITE_TAC[]);;

(* word_add evaluation in general form. *)
let VAL_WORD_ADD_GENERIC = prove
 (`!(x:int32) (y:int32). val x + val y < 2 EXP 32 ==> val(word_add x y) = val x + val y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_32] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

let WORD_ADD_GENERIC = prove
 (`!(x:int32) (y:int32). val x + val y < 2 EXP 32 ==> word_add x y = word(val x + val y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let WORD_ADD_WORD_NUM = prove
 (`!(x:int32) a. val x + a < 2 EXP 32 ==> word_add x (word a:int32) = word(val x + a)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 32 = a` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

(* Trivial byte bounds, frequently needed when stepping. *)
let VAL_BYTE_LT_256 = prove
 (`!(a:byte). val a < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `a:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let NIBBLE_BOUNDS = prove
 (`!(b:byte). val b MOD 16 < 16 /\ val b DIV 16 < 16`,
  GEN_TAC THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC;
    MP_TAC(SPECL [`val(b:byte)`; `16`] DIV_LT) THEN ASM_ARITH_TAC]);;

(* val(word_zx b) = val b for byte zx to wider widths. Used in scalar tail *)
(* and main body when reading bytes from memory and zero-extending.         *)
let VAL_WORD_ZX_BYTE_INT16 = prove
 (`!(b:byte). val(word_zx b:int16) = val b`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16] THEN ARITH_TAC);;

let VAL_WORD_ZX_BYTE_INT32 = prove
 (`!(b:byte). val(word_zx b:int32) = val b`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_32] THEN ARITH_TAC);;

let VAL_WORD_ZX_BYTE_INT64 = prove
 (`!(b:byte). val(word_zx b:int64) = val b`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_64] THEN ARITH_TAC);;

(* SHR x 8 / SHR x 4: val of result. Used when scalar tail does            *)
(* `shr r11d, 4` (shift mask byte) or main loop does `shr r8d, 8`.         *)
let VAL_WORD_USHR_8_INT32 = prove
 (`!(x:int32). val(word_ushr x 8) = val x DIV 256`,
  REWRITE_TAC[VAL_WORD_USHR] THEN ARITH_TAC);;

let VAL_WORD_USHR_4_INT32 = prove
 (`!(x:int32). val(word_ushr x 4) = val x DIV 16`,
  REWRITE_TAC[VAL_WORD_USHR] THEN ARITH_TAC);;

(* Low byte of int32 always <= 255 (used in popcnt low8 bounds). *)
let VAL_WORD_SUBWORD_BYTE_LE_255 = prove
 (`!(x:int32). val(word_subword x (0,8):byte) <= 255`,
  GEN_TAC THEN MP_TAC(ISPEC `word_subword (x:int32) (0,8):byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* word_add evaluation when both summands fit in 256 (bounded sub-iter case)*)
let VAL_WORD_ADD_LE_256 = prove
 (`!a b:num. a + b <= 256
            ==> val(word_add (word a:int32) (word b:int32):int32) = a + b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 32 = a /\ b MOD 2 EXP 32 = b`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* CMP $9 instruction bridges: nibble val < 9 vs val >= 9.                  *)
let VAL_WORD_LT_9_NOT_GE = prove
 (`!a:num. a < 9 ==> ~(9 <= val(word a:int32))`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 32 = a` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let VAL_WORD_GE_9 = prove
 (`!a:num. ~(a < 9) /\ a < 2 EXP 32 ==> 9 <= val(word a:int32)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 32 = a` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* INC instruction evaluation: word_add (word a) (word 1) = word(a+1)      *)
(* and val(...) = a + 1, when a is small enough.                            *)
let WORD_ADD_INC_INT32 = prove
 (`!a:num. a < 2 EXP 32 ==> word_add (word a:int32) (word 1):int32 = word(a + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `a < 2 EXP 32 ==> 1 < 2 EXP 32`] THEN
  REWRITE_TAC[ARITH_RULE `a < 2 EXP 32 <=> a <= 2 EXP 32 - 1`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VAL_WORD_INC_LE_256 = prove
 (`!a:num. a <= 256 ==> val(word_add (word a:int32) (word 1):int32) = a + 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `a MOD 4294967296 = a` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* Memory read of byte k of input list via num_of_wordlist representation. *)
let NUM_OF_WORDLIST_DIV_MOD_VAL_EL = prove
 (`!(l:byte list) (n:num).
     n < LENGTH l
     ==> num_of_wordlist l DIV 2 EXP (8 * n) MOD 256 = val (EL n l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EL n (l:byte list) = word(num_of_wordlist l DIV 2 EXP (8 * n)):byte`
    SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:byte list`; `n:num`] EL_NUM_OF_WORDLIST) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN ARITH_TAC);;

(* JAE-taken bridges: when val >= bound, the conditional jump fires. Used  *)
(* in the scalar tail for the early exits at pc+316 (cmp eax 256) and       *)
(* pc+324 (cmp ecx 136).                                                    *)
let VAL_WORD_GE_BOUND = prove
 (`!a b:num. b <= a /\ a < 2 EXP 32 ==> b <= val(word a:int32)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let VAL_WORD_GE_256 = prove
 (`!a:num. 256 <= a /\ a < 2 EXP 32 ==> 256 <= val(word a:int32)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:num`; `256`] VAL_WORD_GE_BOUND) THEN
  ASM_REWRITE_TAC[]);;

let VAL_WORD_GE_136 = prove
 (`!a:num. 136 <= a /\ a < 2 EXP 32 ==> 136 <= val(word a:int32)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:num`; `136`] VAL_WORD_GE_BOUND) THEN
  ASM_REWRITE_TAC[]);;

(* When the SIMD loop terminates because pos crosses the buf boundary       *)
(* (i.e. 256 < 16*N), N must be exactly 17 (so pos = 16*17 = 272, hitting   *)
(* the cmp $256, ecx exit on the 17th outer iteration).                     *)
let SCALAR_TAIL_N_EQ_17 = prove
 (`!N (inlist:byte list).
     LENGTH inlist = 272 /\
     ~(N = 0) /\
     256 < 16 * N /\
     (!m. m < N ==> 16 * m <= 256 /\
          LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * m) inlist):int16 list) <= 248)
     ==> N = 17`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `N <= 17` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> N - 1 < N`] THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* outlist0 length bound at scalar tail entry: at most 280 (worst case      *)
(* prefix length 248 + one more 16-byte chunk contributes at most 32).       *)
let LENGTH_OUTLIST0_LE_280 = prove
 (`!N (inlist:byte list).
     LENGTH inlist = 272 /\
     ~(N = 0) /\
     16 * (N - 1) <= 256 /\
     LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * (N-1)) inlist):int16 list) <= 248
     ==> LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST(0, 16*N) inlist):int32 list) <= 280`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  SUBGOAL_THEN `16 * N = 16 * (N - 1) + 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `16 * (N - 1) + 16 = 0 + 16 * (N - 1) + 16`] THEN
  REWRITE_TAC[SUB_LIST_SPLIT] THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND; ADD_CLAUSES] THEN
  MP_TAC(ISPEC `SUB_LIST(16 * (N - 1), 16) inlist:byte list`
              LENGTH_REJ_NIBBLES_ETA4) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; SUB_LIST_CLAUSES; REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN
  ASM_ARITH_TAC);;

(* JA-not-taken bridges: when val < bound is false (i.e. val <= bound),     *)
(* the conditional jump above does not fire. Used to prove RIP advances     *)
(* past JAs in body proof (cmp eax 248, ja done) and (cmp ecx 120, ja done).*)
let VAL_WORD_LE_NOT_LT = prove
 (`!a b:num. a <= b /\ b < 2 EXP 32 ==> ~(b < val(word a:int32))`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 32 = a` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let VAL_WORD_LE_248_NOT_LT = prove
 (`!a:num. a <= 248 ==> ~(248 < val(word a:int32))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `248`] VAL_WORD_LE_NOT_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `248 < 2 EXP 32`]);;

let VAL_WORD_LE_256_NOT_LT = prove
 (`!a:num. a <= 256 ==> ~(256 < val(word a:int32))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `256`] VAL_WORD_LE_NOT_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 < 2 EXP 32`]);;

(* val(word_zx) narrowing from int64 to int32 for small values. The x86     *)
(* loop counters live in 64-bit registers (RAX/RCX); the `cmp $imm32, %e_x`  *)
(* zero-extends the 32-bit view, so the model carries word_zx(word a:int64). *)
let VAL_WORD_ZX_64_32 = prove
 (`!a. a < 2 EXP 32 ==> val(word_zx(word a:int64):int32) = a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `a MOD 2 EXP 64 = a` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

(* Loop-guard fall-through bridge: after `cmp $k, %e_x` with the 64-bit      *)
(* register holding `word a` (a <= k <= 2^32-1), the `ja` (jump-if-above,    *)
(* unsigned >) is NOT taken. The x86 model emits the taken-condition as      *)
(* `~(~EQ \/ ZF)` where EQ is the CF-via-int-equality and ZF the zero test;  *)
(* this lemma proves `~EQ \/ ZF` holds so the taken-condition is false and   *)
(* execution falls through. Stated with `word a:int64` (the register width)  *)
(* and `&`:int (int_of_num) to match the model's flag terms EXACTLY, so      *)
(* X86_STEPS_TAC resolves the conditional RIP automatically when this lemma  *)
(* (instantiated for the right a,k) is in the assumptions. Used at all five  *)
(* cmp/ja sites in the SIMD loop body (the two loop-head guards on ctr<=248  *)
(* and pos<=256, plus the three mid-iteration early-exit checks).            *)
let JA_NOT_TAKEN_LE = prove
 (`!a k:num. a <= k /\ k < 2 EXP 32
     ==> ~(&(val(word_zx(word a:int64):int32)):int - &k =
           &(val(word_sub (word_zx(word a:int64):int32) (word k:int32)))) \/
         val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word k:int32) = k` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `a = k:num` THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN
    SUBGOAL_THEN `word_zx(word k:int64):int32 = word k` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD_ZX_64_32] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_32] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]];
    DISJ1_TAC THEN
    SUBGOAL_THEN `a < k` ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) =
                  a + 2 EXP 32 - k` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; REFL_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&a:int < &k` MP_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`a + 2 EXP 32 - k`,`m:num`) THEN INT_ARITH_TAC]);;

(* word_add evaluation when both summands are bounded by 248 (and thus the   *)
(* sum is also bounded). Used to compute exact RAX value after `add eax, r9d`*)
(* in sub-iter 1 of the body proof.                                          *)
let VAL_WORD_ADD_LE_248 = prove
 (`!a b. a + b <= 248
         ==> val(word_add (word a:int32) (word b:int32):int32) = a + b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 32 = a /\ b MOD 2 EXP 32 = b`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* num_of_wordlist for short int32 lists. Used when each scalar tail        *)
(* iteration writes one or two int32 to memory.                              *)
let NUM_OF_WORDLIST_SINGLETON_INT32 = prove
 (`!(x:int32). num_of_wordlist [x] = val x`,
  REWRITE_TAC[num_of_wordlist] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_PAIR_INT32 = prove
 (`!(x:int32) (y:int32). num_of_wordlist [x;y] = val x + 2 EXP 32 * val y`,
  REWRITE_TAC[num_of_wordlist; DIMINDEX_32] THEN ARITH_TAC);;

(* Total output bound: full input gives at most 2 * LENGTH int32s.          *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_272 = prove
 (`!(inlist:byte list).
     LENGTH inlist = 272
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES inlist :int32 list) <= 544`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `inlist:byte list` LENGTH_REJ_SAMPLE_ETA4_BYTES_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Step lemma: outlen after processing one more byte equals current outlen   *)
(* + contribution of that byte (0, 1, or 2 elements).                        *)
let SUB_LIST_STEP_BYTE = prove
 (`!(l:byte list) (k:num).
     k < LENGTH l
     ==> SUB_LIST(0, k+1) l = APPEND (SUB_LIST(0, k) l) [EL k l]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`; `1`; `0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `0 + k = k`] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[SUB_LIST_1]);;

let REJ_SAMPLE_ETA4_BYTES_STEP_1 = prove
 (`!(l:byte list) (k:num).
     k < LENGTH l
     ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, k+1) l) =
         APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, k) l))
                (REJ_SAMPLE_ETA4_BYTES [EL k l])`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_STEP_BYTE; REJ_SAMPLE_ETA4_BYTES_APPEND]);;

let LENGTH_REJ_SAMPLE_ETA4_BYTES_STEP_1 = prove
 (`!(inlist:byte list) k.
     k < LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, k+1) inlist):int32 list) =
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, k) inlist):int32 list) +
         LENGTH(REJ_SAMPLE_ETA4_BYTES [EL k inlist]:int32 list)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REJ_SAMPLE_ETA4_BYTES_STEP_1; LENGTH_APPEND]);;

(* SUB_LIST capping: when output already has length <= 256, the SUB_LIST(0, *)
(* 256) cap is a no-op. Used in scalar-tail final-state composition.        *)
let SUB_LIST_256_LE = prove
 (`!(l:int32 list). LENGTH l <= 256 ==> SUB_LIST(0, 256) l = l`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `m = LENGTH (l:int32 list)` THEN
  MP_TAC(ISPECL [`l:int32 list`; `m:num`; `256 - m`; `0`] SUB_LIST_SPLIT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + a = a`] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= 256 ==> m + (256 - m) = 256`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[SUB_LIST_LENGTH; SUB_LIST_TRIVIAL; LE_REFL; APPEND_NIL] THEN
  UNDISCH_TAC `LENGTH (l:int32 list) = m` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_LIST_LENGTH] THEN
  MP_TAC(ISPECL [`l:int32 list`; `LENGTH (l:int32 list)`;
                 `256 - LENGTH (l:int32 list)`] SUB_LIST_TRIVIAL) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[APPEND_NIL]);;

(* When the input has its full known length, SUB_LIST(0, that length) is a   *)
(* no-op: applies to LENGTH inlist = 272.                                    *)
let SUB_LIST_BYTE_272 = prove
 (`!(l:byte list). LENGTH l = 272 ==> SUB_LIST(0, 272) l = l`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `LENGTH (l:byte list) = 272` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC SUB_LIST_LENGTH);;

(* The asm computes `4 - low_nibble(b)` directly as int32, while the spec   *)
(* uses `word_sx (word_sub (word 4:int16) (word(val b MOD 16))):int32`.     *)
(* For accepted nibbles (val b MOD 16 < 9), these are equal.                *)
let SCALAR_LOW_NIBBLE_STORE_EQ_SPEC = prove
 (`!(b:byte).
     val b MOD 16 < 9
     ==> word_sub (word 4:int32) (word_and (word_zx b:int32) (word 15:int32)):int32 =
         word_sx(word_sub (word 4:int16) (word(val b MOD 16)):int16):int32`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(word_and (word_zx (b:byte):int32) (word 15:int32):int32) =
                (word(val(b:byte) MOD 16):int32)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_15_INT32] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    STRIP_TAC THEN MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`val(b:byte)`; `16`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC WORD_SUB_4_NIBBLE_INT32_AS_SX THEN ASM_REWRITE_TAC[]);;

(* High nibble counterpart: asm's `4 - high_nibble(b)` int32 equals spec's  *)
(* word_sx of int16 form, when high nibble is accepted.                     *)
let SCALAR_HIGH_NIBBLE_STORE_EQ_SPEC = prove
 (`!(b:byte).
     val b DIV 16 < 9
     ==> word_sub (word 4:int32)
                  (word_and (word_ushr (word_zx b:int32) 4) (word 15:int32)):int32 =
         word_sx(word_sub (word 4:int16) (word(val b DIV 16)):int16):int32`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(word_and (word_ushr (word_zx (b:byte):int32) 4) (word 15:int32):int32) =
                (word(val(b:byte) DIV 16):int32)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR_4_AND_15_INT32] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    STRIP_TAC THEN MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`val(b:byte)`; `16`] DIV_LT) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC WORD_SUB_4_NIBBLE_INT32_AS_SX THEN ASM_REWRITE_TAC[]);;

(* Per-byte helpers for the scalar tail proof. Three cases by which nibble *)
(* (low and/or high) is < 9 (accepted) or >= 9 (rejected).                  *)
let REJ_SAMPLE_ETA4_BYTES_1_REJECT_BOTH = prove
 (`!b:byte. ~(val b MOD 16 < 9) /\ ~(val b DIV 16 < 9)
            ==> REJ_SAMPLE_ETA4_BYTES [b] = []`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA4_BYTES_1_LOW_ONLY = prove
 (`!b:byte. val b MOD 16 < 9 /\ ~(val b DIV 16 < 9)
            ==> REJ_SAMPLE_ETA4_BYTES [b] =
                [word_sx(word_sub (word 4:int16) (word(val b MOD 16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA4_BYTES_1_HIGH_ONLY = prove
 (`!b:byte. ~(val b MOD 16 < 9) /\ val b DIV 16 < 9
            ==> REJ_SAMPLE_ETA4_BYTES [b] =
                [word_sx(word_sub (word 4:int16) (word(val b DIV 16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA4_BYTES_1_BOTH = prove
 (`!b:byte. val b MOD 16 < 9 /\ val b DIV 16 < 9
            ==> REJ_SAMPLE_ETA4_BYTES [b] =
                [word_sx(word_sub (word 4:int16) (word(val b MOD 16))):int32;
                 word_sx(word_sub (word 4:int16) (word(val b DIV 16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; APPEND]);;

let LENGTH_REJ_SAMPLE_ETA4_BYTES_1 = prove
 (`!b:byte. LENGTH(REJ_SAMPLE_ETA4_BYTES [b] :int32 list) =
            (if val b MOD 16 < 9 then 1 else 0) +
            (if val b DIV 16 < 9 then 1 else 0)`,
  GEN_TAC THEN REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; LENGTH_APPEND] THEN
  COND_CASES_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* CONS step for REJ_SAMPLE_ETA4_BYTES.                                     *)
let REJ_SAMPLE_ETA4_BYTES_CONS = prove
 (`!(b:byte) (rest:byte list).
     REJ_SAMPLE_ETA4_BYTES (CONS b rest) =
     APPEND (REJ_SAMPLE_ETA4_BYTES [b]) (REJ_SAMPLE_ETA4_BYTES rest)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`[b:byte]`; `rest:byte list`] REJ_SAMPLE_ETA4_BYTES_APPEND) THEN
  REWRITE_TAC[APPEND]);;

(* SUB_LIST step: extending the prefix by one element. Used in the scalar  *)
(* tail's loop invariant where each iteration advances pos by 1.            *)
(* WOP-derived bound: niblen <= 280 (i.e., 248 + 32, since each iter adds at most 32) *)
let NIBLEN_BOUND_FROM_WOP = prove
 (`!inlist:byte list. !N.
   0 < N /\
   (!m. m < N ==> 16 * (m + 1) <= LENGTH inlist /\
        LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*m) inlist)) <= 248)
   ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*N) inlist):int16 list) <= 280`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `N - 1 < N <=> 0 < N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * N = 0 + 16 * (N - 1) + 16` SUBST1_TAC THENL
   [UNDISCH_TAC `0 < N` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES] THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN
  MP_TAC(ISPEC `SUB_LIST(16*(N-1),16) inlist:byte list`
    LENGTH_REJ_NIBBLES_ETA4) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  UNDISCH_TAC
   `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(N-1)) inlist):int16 list) <= 248` THEN
  ARITH_TAC);;

(* ========================================================================= *)
(* Main CORRECT theorem.                                                     *)
(*                                                                           *)
(* Status: Phase 0-2 (setup, WOP, ENSURES_WHILE_UP2_TAC) PROVED.             *)
(*         Subgoal 1 (preamble pc -> pc + 56) FULLY PROVED.                    *)
(*         Subgoal 2 (loop body pc + 56 -> pc + 56/pc + 318) CHEATed.              *)
(*         Subgoal 3 (post-loop scalar tail pc + 318 -> end) CHEATed.          *)
(*                                                                           *)
(* Loop body structure: 4 sub-iterations of (vextracti128/vpsrldq +         *)
(* movzbl + vmovq + vpshufb + vpmovsxbd + vmovdqu + popcntl + add + shr +   *)
(* add + cmp + ja). Each sub-iter processes 8 nibbles using table lookup.   *)
(* Total iteration: 16 bytes consumed, up to 32 nibbles produced.            *)
(* ========================================================================= *)

(* x86 calling convention: rdi=res, rsi=buf, rdx=table.
   Note: x86 uses fixed buflen of 136 bytes (MLD_AVX2_REJ_UNIFORM_ETA4_BUFLEN),
   not a parameter like aarch64. *)

(* ========================================================================= *)
(* Body helper lemma: ensures-shape closing the loop body i -> i+1.          *)
(* From state at pc + 56 (loop head, after WOP-derived precondition for i)     *)
(* to state at pc + 56 (next iter) or pc + 318 (loop exit).                      *)
(* The proof of this lemma is admitted (CHEAT_TAC). To close it fully:       *)
(*  - REABBREV pattern (mask at s22, r10val0 at s28) to capture popcnt;     *)
(*  - RAX_BOUND_AFTER_POPCNT_ADD_DIRECT to convert RAX to canonical form;   *)
(*  - sub-iter pattern repeated 4x (vextracti/vpsrldq + vpshufb + vmovdqu); *)
(*  - composition of 4 sub-iters into REJ_SAMPLE_ETA4_BYTES SUB_LIST step.  *)
(*                                                                           *)
(* VALIDATED loop-guard prologue (proven interactively, ready to inline).    *)
(* Lands at RIP = pc + 79 (the vpmovzxbw that starts the SIMD body), with    *)
(* RAX = word outlen0, RCX = word(16*i), memory contracts intact:            *)
(*   REPEAT GEN_TAC THEN STRIP_TAC THEN                                      *)
(*   ABBREV_TAC `outlist0 = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist)`  *)
(*   ABBREV_TAC `outlen0 = LENGTH(outlist0:int32 list)` THEN                 *)
(*   SUBGOAL outlen0 <= 248  (EXPAND + REJ_SAMPLE_ETA4_BYTES;LENGTH_MAP) THEN*)
(*   ENSURES_INIT_TAC "s0" THEN                                             *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH outlist0 = outlen0`]) THEN  *)
(*   split the RAX/RCX/mem conjunct into separate assumptions; THEN         *)
(*   MP_TAC(SPECL [`outlen0`;`248`] JA_NOT_TAKEN_LE) + ANTS, and            *)
(*   MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) + ANTS, both DISCH_TAC.   *)
(*   With both disjunction facts in the assumptions in the matching int64/  *)
(*   int form, X86_STEPS_TAC EXEC (1--4) resolves BOTH cmp/ja guards        *)
(*   automatically -> read RIP s4 = word(pc + 79). KEY: JA_NOT_TAKEN_LE     *)
(*   must use `word a:int64` (register width) and `&`:int so the flag terms *)
(*   match EXACTLY; a :int32 / :real mis-typing prints identically but      *)
(*   fails to unify (the classic invisible-type-mismatch trap).             *)
(* Then X86_STEPS_TAC EXEC (1--11) carries through the two guards plus the  *)
(* 7-instruction SIMD setup (vpmovzxbw, vpsllw, vpor, vpand, vpsubb, vpsubb, *)
(* vpmovmskb), landing at read RIP = word(pc + 110) (= the vextracti128     *)
(* that starts sub-iter 1) -- VALIDATED interactively.                      *)
(*                                                                           *)
(* VALIDATED DIGITIZATION (solves the opaque-YMM0 obstacle): right after    *)
(* ENSURES_INIT_TAC "s0", before the guard MP_TACs, do                      *)
(*   MP_TAC(SPECL [`buf:int64`;`272`;`inlist:byte list`;`i:num`;`s0:x86state`]*)
(*     SUB_LIST_16_BYTES_FROM_INT128) THEN                                  *)
(*   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ...16*i<=256...ARITH_TAC; ALL_TAC]*)
(*   THEN ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf           *)
(*     (word(16*i)))) s0` THEN DISCH_TAC.                                    *)
(* Then chunk0 threads through X86_STEPS_TAC (1--11) intact (preserved as    *)
(* read(memory:>bytes128(word_add buf (word(16*i)))) sN = chunk0), AND the   *)
(* spec-input bridge SUB_LIST(16*i,16) inlist = [16 byte-subwords of chunk0] *)
(* sits in the assumptions -- so the vpmovzxbw load result is expressed via  *)
(* chunk0, not opaque. CONFIRMED to s12 (vextracti128). From here REABBREV   *)
(* the SIMD register values (YMM0 after vpand, R8 after vpmovmskb, YMM5/6    *)
(* per sub-iter) and apply the proven value lemmas at each vmovdqu store.    *)
(*                                                                           *)
(* SIMD SEMANTIC CORE -- ALL VALUE/COUNT LEMMAS NOW PROVEN (state-free):    *)
(*  (a) [DONE] SUB_LIST_16_BYTES_FROM_INT128: the vpmovzxbw load = the 16   *)
(*      input bytes SUB_LIST(16*i,16) inlist.                               *)
(*  (b) [DONE] nibble extraction: VPSLLW_VPOR_VPAND_INT16_NIBBLES (per      *)
(*      byte -> [lo;hi] nibbles), VPMOVZXBW_LANE_EXTRACT / _BYTE_EXTRACT.   *)
(*  (c) [DONE] bound + mask: VPSUBB_SIGN_BIT_LT_9, VMOVMSKB_BYTE_EQ_64,     *)
(*      POPCNT_EQ_LENGTH_FILTER_8, POPCNT_NIBBLES_4_BYTES_BRIDGE.           *)
(*  (d) [DONE] pshufb compaction: PSHUFB_GATHER_BYTE, PSHUFB_LANE_EXTRACT,  *)
(*      PSHUFB_TABLE_GATHER(_8), TABLE_PREFIX_ACC (256-case keystone),      *)
(*      PSHUFB_OUT_BYTE/_LIST, PSHUFB_ACCEPTED_PREFIX(_NUM): the first      *)
(*      popcount(m) output bytes = source bytes at ACC_IDX m. Plus          *)
(*      VPMOVSXBD_LANE_EXTRACT (byte->int32 sx) and GATHER_FILTERED_IDX_8   *)
(*      (gather-at-accepted-positions = FILTER) and                        *)
(*      WORD_SUB_4_NIBBLE_INT32_AS_SX (eta value = spec coefficient).       *)
(*  (e) [DONE] composition arithmetic: SUBITER_OUTLEN_STEP_4 (outlen += sum *)
(*      of 4 popcounts) and REJ_SAMPLE_ETA4_BYTES_STEP_16 (memory append),  *)
(*      via REJ_SAMPLE_ETA4_BYTES_16_AS_4 / REJ_NIBBLES_ETA4_APPEND.        *)
(*                                                                          *)
(* REMAINING: only the simulator-stepping ASSEMBLY -- instantiate the above *)
(* at the concrete instruction effects across the 4 sub-iters.             *)
(* KEY TECHNIQUE (validated): the prologue X86_STEPS_TAC (1--11) reaches    *)
(* RIP=pc+110 but the stepper DISCARDS the YMM0/R8 values (input inlist is  *)
(* abstract, so the vpmovzxbw load is opaque and falls out of the assumption*)
(* set -- only MAYCHANGE[YMM0;YMM1;R8] remains). To track them: BEFORE      *)
(* stepping the load, digitize the buffer with SUB_LIST_16_BYTES_FROM_INT128*)
(* (instantiated buf,272,inlist,i) and ABBREV the 128-bit chunk read at     *)
(* word_add buf (word(16*i)); then the load result is that abbreviation and *)
(* the stepper carries YMM0 symbolically. REABBREV YMM0 after the vpand     *)
(* (instr ~8) and R8 after vpmovmskb (instr ~11) -- as in PR1014's          *)
(* rej_uniform body. Then per sub-iter: REABBREV the pshufb result, apply   *)
(* PSHUFB_ACCEPTED_PREFIX_NUM + VPMOVSXBD_LANE_EXTRACT to the vmovdqu store, *)
(* RAX_BOUND_AFTER_POPCNT_ADD_DIRECT for the popcount add, JA_NOT_TAKEN_LE  *)
(* for the mid-iter guard; compose 4 via the (e) lemmas.                   *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA4_BODY_CHEAT = prove
 (`!res buf table (inlist:byte list) pc N (i:num) stackpointer.
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        ~(N = 0) /\
        i < N /\ ~(i = N) /\ 0 < N /\
        16 * i <= 256 /\
        LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * i) inlist)) <= 248
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 56) /\
                  read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  (let outlist = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist) in
                   let outlen = LENGTH outlist in
                   read RAX s = word outlen /\
                   read RCX s = word(16*i) /\
                   read(memory :> bytes(res, 4 * outlen)) s = num_of_wordlist outlist))
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(if i + 1 < N then pc + 56 else pc + 318) /\
                  read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  (let outlist =
                     REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16 * (i + 1)) inlist) in
                   let outlen = LENGTH outlist in
                   read RAX s = word outlen /\
                   read RCX s = word(16 * (i + 1)) /\
                   read(memory :> bytes(res,4 * outlen)) s =
                     num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  CHEAT_TAC);;

(* ========================================================================= *)
(* Scalar tail helper lemma: ensures-shape from pc + 318 to function end.      *)
(* Handles both Case A (jae fires when outlen0 >= 256) and Case B (scan      *)
(* loop over remaining bytes). Proof admitted (CHEAT_TAC).                   *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_CHEAT = prove
 (`!res buf table (inlist:byte list) pc N stackpointer.
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 407) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        (256 < 16 * N \/
         248 < LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * N) inlist):int16 list)) /\
        (!m. m < N
             ==> 16 * m <= 256 /\
                 LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * m) inlist)) <= 248) /\
        ~(N = 0)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 318) /\
                  read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  (let outlist = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist) in
                   let outlen = LENGTH outlist in
                   read RAX s = word outlen /\
                   read RCX s = word(16 * N) /\
                   read(memory :> bytes(res, 4 * outlen)) s = num_of_wordlist outlist))
             (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                   let outlen = LENGTH outlist in
                   read RAX s = word outlen /\
                   read(memory :> bytes(res, 4 * outlen)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  CHEAT_TAC);;

let MLDSA_REJ_UNIFORM_ETA4_CORRECT = prove
 (`!res buf table (inlist:byte list) pc.
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
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                    num_of_wordlist outlist)
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  (* ===================================================================== *)
  (* Phase 0: Setup - introduce variables, strip assumptions               *)
  (*                                                                       *)
  (* Concretize LENGTH mldsa_rej_uniform_eta4_tmc to 407 in the nonoverlap *)
  (* hypotheses so that ORTHOGONAL_COMPONENTS_TAC can handle them later in *)
  (* the body's vmovdqu store.                                            *)
  (* ===================================================================== *)
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `buf:int64`; `table:int64`;
    `inlist:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
  STRIP_TAC THEN
  GHOST_INTRO_TAC `stackpointer:int64` `read RSP` THEN

  (* ===================================================================== *)
  (* Phase 1: WOP to find smallest N where loop terminates.                *)
  (*                                                                       *)
  (* Loop checks: cmp eax,0xF8 (248); cmp ecx,0x100 (256).                 *)
  (* Each outer iter adds 16 to ecx (4 sub-iters * 4 each).               *)
  (* Exit: ecx > 256 OR ctr > 248.                                        *)
  (* WOP gives smallest N where loop must exit. Witness: i = 17 makes     *)
  (* 16*i = 272 > 256, satisfying the disjunction.                        *)
  (* ===================================================================== *)
  SUBGOAL_THEN
   `?i. 256 < 16 * i \/
        248 < LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * i) inlist):int16 list)`
  MP_TAC THENL
   [EXISTS_TAC `17:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT] th)) THEN

  (* N must be > 0 because at i=0 both conditions are vacuously false *)
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  (* ===================================================================== *)
  (* Phase 2: ENSURES_WHILE_UP2_TAC for the SIMD loop                     *)
  (*                                                                       *)
  (* Loop head: pc + 56 (cmp eax,0xF8)                                    *)
  (* Loop exit: pc + 318 (scalar code starts here)                        *)
  (* ===================================================================== *)
  ENSURES_WHILE_UP2_TAC `N:num` `pc + 56` `pc + 318`
   `\i s. read RSP s = stackpointer /\
          read (memory :> bytes (buf, 272)) s = num_of_wordlist inlist /\
          read (memory :> bytes (table,2048)) s =
            num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
          read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
          let outlist = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist) in
          let outlen = LENGTH outlist in
          read RAX s = word outlen /\
          read RCX s = word(16*i) /\
          read(memory :> bytes(res, 4 * outlen)) s = num_of_wordlist outlist` THEN
  ASM_REWRITE_TAC[LT_REFL] THEN REPEAT CONJ_TAC THENL

   [(* ================================================================= *)
    (* Subgoal 1: Pre-loop setup (preamble pc -> pc + 56)                *)
    (* Instructions 1-12: endbr64 (the *second* one — the first was     *)
    (* trimmed by define_trimmed), 3x (mov r8d / vmovd / vpbroadcastd), *)
    (* then xor eax,eax and xor ecx,ecx.                                *)
    (* ================================================================= *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES;
                REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4;
                NIBBLES_OF_BYTES; FILTER; MAP; LENGTH;
                num_of_wordlist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN
    CONV_TAC WORD_REDUCE_CONV;

    (* ================================================================= *)
    (* Subgoal 2: Loop body (i -> i+1) — delegated to BODY_CHEAT helper. *)
    (* ================================================================= *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < N`) o
      check (fun th -> is_forall(concl th))) THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `table:int64`;
                  `inlist:byte list`; `pc:num`; `N:num`; `i:num`;
                  `stackpointer:int64`] MLDSA_REJ_UNIFORM_ETA4_BODY_CHEAT) THEN
    ASM_REWRITE_TAC[];

    (* ================================================================= *)
    (* Subgoal 3: Post-loop (scalar tail) — delegated to TAIL_CHEAT.     *)
    (* ================================================================= *)
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `table:int64`;
                  `inlist:byte list`; `pc:num`; `N:num`;
                  `stackpointer:int64`]
                 MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_CHEAT) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Strengthened CORRECT theorem with array_bound (CBMC postcondition).       *)
(* This is the form needed by the subroutine wrappers.                       *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND = prove
 (`!res buf table (inlist:byte list) pc.
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
              read(memory :> bytes(table,2048)) s =
                num_of_wordlist mldsa_rej_uniform_table)
         (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
              (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
               let outlen = LENGTH outlist in
               outlen <= 256 /\
               C_RETURN s = word outlen /\
               read(memory :> bytes(res,4 * outlen)) s =
                 num_of_wordlist outlist /\
               (!i. i < outlen
                    ==> ival(EL i outlist:int32) < &5 /\
                        -- &5 < ival(EL i outlist:int32))))
         (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_STRENGTHEN_POST_X86 THEN
  EXISTS_TAC
   `\s:x86state.
      read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
      (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES (inlist:byte list)) in
       let outlen = LENGTH outlist in
       C_RETURN s = word outlen /\
       read(memory :> bytes(res:int64,4 * outlen)) s =
         num_of_wordlist outlist)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MLDSA_REJ_UNIFORM_ETA4_CORRECT THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC LENGTH_SUB_LIST_REJ_SAMPLE_ETA4_BYTES; ALL_TAC] THEN
    MATCH_ACCEPT_TAC REJ_SAMPLE_ETA4_BYTES_EL_BOUND]);;

(* ========================================================================= *)
(* Subroutine wrappers                                                       *)
(* ========================================================================= *)

(* Concrete-length variant of CORRECT_BOUND used by X86_PROMOTE_RETURN_NOSTACK_TAC *)
let MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND_CONCRETE =
  CONV_RULE(REWRITE_CONV[LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC; fst MLDSA_REJ_UNIFORM_ETA4_EXEC])
    MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND;;

(* Subroutine wrapper for the trimmed mc (NOIBT). Postconditions are kept   *)
(* in sync with the CBMC contract for mld_rej_uniform_eta4_avx2_asm in      *)
(*   dev/x86_64/src/arith_native_x86_64.h                                   *)
(*   mldsa/src/native/x86_64/src/arith_native_x86_64.h                      *)
(* CBMC ensures:                                                            *)
(*   ensures(return_value <= MLDSA_N)              -- outlen <= 256         *)
(*   ensures(array_bound(r, 0, return_value, -4, 4)) -- coefficients        *)
(*                                                       in [-4, 4]        *)
(* type_invention_error must be off when invoking X86_PROMOTE_RETURN_NOSTACK_TAC *)
(* because the underlying X86_ADD_RETURN_NOSTACK_TAC contains a stale       *)
(* `read PC s = a \/ Q` term-match that needs type-variable invention.      *)
let MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_CORRECT =
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) pc stackpointer returnaddress.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (res, 1024) /\
        nonoverlapping (stackpointer, 8) (buf, 272) /\
        nonoverlapping (stackpointer, 8) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (word pc, LENGTH mldsa_rej_uniform_eta4_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta4_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (let outlist = SUB_LIST(0,256)
                      (REJ_SAMPLE_ETA4_BYTES inlist) in
                   let outlen = LENGTH outlist in
                   outlen <= 256 /\
                   C_RETURN s = word outlen /\
                   read(memory :> bytes(res,4 * outlen)) s =
                     num_of_wordlist outlist /\
                   (!i. i < outlen
                        ==> ival(EL i outlist:int32) < &5 /\
                            -- &5 < ival(EL i outlist:int32))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
    REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
    X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_rej_uniform_eta4_tmc
      MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND_CONCRETE) in
  type_invention_error := saved_tic;
  th;;

(* TODO: ADD_IBT_RULE wrapper after CORRECT is fully proven
let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_CORRECT =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_CORRECT;;
*)

(* ========================================================================= *)
(* Memory safety theorem (skeleton)                                          *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA4_MEMSAFE = prove
 (`!res buf table (inlist:byte list) e pc.
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
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,272; table,2048]
                       [res,1024]))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  CHEAT_TAC);;

let MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_MEMSAFE = prove
 (`!res buf table (inlist:byte list) e pc stackpointer returnaddress.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_mc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_mc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_mc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (res, 1024) /\
        nonoverlapping (stackpointer, 8) (buf, 272) /\
        nonoverlapping (stackpointer, 8) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (word pc, LENGTH mldsa_rej_uniform_eta4_mc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,272; table,2048]
                       [res,1024]))
             (MAYCHANGE [RIP; RSP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  CHEAT_TAC);;

(* TODO: ADD_IBT_RULE wrapper after MEMSAFE is fully proven
let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_MEMSAFE =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_MEMSAFE;;
*)
