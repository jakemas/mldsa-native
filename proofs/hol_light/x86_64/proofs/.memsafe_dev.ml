(* ========================================================================= *)
(* MEMSAFE proof for rej_uniform_eta4 (x86_64).                              *)
(* Adapted from PR #1014's x86 MLDSA_REJ_UNIFORM_MEMSAFE template.           *)
(* Load AFTER the main eta4 file + consttime.ml.                             *)
(* ========================================================================= *)

let allowed_vars_e : term list ref = ref [];;
let NIL_IMPLIES_APPEND_EQ =
  prove(`!(l:(A)list) m m'. m = m' /\ [] = l ==> m = APPEND l m'`, MESON_TAC[APPEND]);;
let EXISTS_E2_TAC allowed_vars_e =
  (MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL [
    REFL_TAC; SAFE_UNIFY_REFL_TAC allowed_vars_e (ref ["f_events_callee"]) ]) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
   TRY (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e (ref ["f_events_callee"])) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e (ref ["f_events_callee"]));;
let DISCHARGE_MEMSAFE_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* Like SIMPLE_ARITH_TAC but allows `val` in assumptions since
   contained_modulo bounds may involve val terms. Filters out
   read/write/word simulation cruft that makes ASM_ARITH_TAC slow. *)
let (MEMSAFE_ARITH_TAC:tactic) =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="]
  and avoiders = ["lowdigits"; "highdigits"; "bigdigit";
                  "read"; "write"; "word"] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n avoiders | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    not(can (find_term avoiderp) tm) in
  let tweak = GEN_REWRITE_RULE TRY_CONV [ARITH_RULE `~(n = 0) <=> 1 <= n`] in
  W(fun (asl,w) ->
    let asl' = filter (fun (_,th) -> filtered(concl th)) asl in
    MAP_EVERY (MP_TAC o tweak o snd) asl' THEN CONV_TAC ARITH_RULE);;

(* Bring `bitval p <= 1` as a MP_TAC hypothesis so MEMSAFE_ARITH_TAC's
   ARITH_RULE can derive bounds on bitval-sum expressions arising from
   VPMOVMSKPS-derived table indices. *)
let MEMSAFE_BITVAL_TAC:tactic =
  W(fun (asl,w) ->
    let bvs = find_terms (fun t ->
      try fst(dest_const(rator t)) = "bitval" with _ -> false) w in
    let bvs = setify bvs in
    MAP_EVERY (fun bv ->
      MP_TAC(SPEC (rand bv) BITVAL_BOUND)) bvs);;

(* ASM-aware version of CONTAINED_TAC for loop-body proofs where
   memory addresses involve symbolic loop variables. Uses MEMSAFE_ARITH_TAC
   which filters assumptions to avoid the performance issues of ASM_ARITH_TAC
   with hundreds of symbolic simulation assumptions. *)
let CONTAINED_ASM_TAC =
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV MOD_DOWN_CONV)) THEN
  REWRITE_TAC[CONTAINED_MODULO_MOD2; CONTAINED_MODULO_LMOD] THEN
  ((GEN_REWRITE_TAC I [CONTAINED_MODULO_REFL] THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC));;

(* Variant of DISCARD_OLDSTATE_TAC that preserves hypotheses about
   `read events sN` regardless of state references inside their RHS.
   Needed because the SIMD loop body's POPCNT operand transitively
   references `read (memory :> bytes256 buf) s4`, which would otherwise
   cause the whole events chain to be erased. *)
let DISCARD_OLDSTATE_KEEP_EVENTS_TAC (s:string) =
  let v = mk_var(s, `:x86state`) in
  let rec unbound_statevars_of_read bound_svars tm =
    match tm with
      Comb(Comb(Const("read",_),cmp),s) ->
        if mem s bound_svars then [] else [s]
    | Comb(a,b) -> union (unbound_statevars_of_read bound_svars a)
                         (unbound_statevars_of_read bound_svars b)
    | Abs(v,t) -> unbound_statevars_of_read (v::bound_svars) t
    | _ -> [] in
  let is_events_hyp tm =
    is_eq tm &&
    (try let l = lhs tm in
         let f, args = strip_comb l in
         fst(dest_const f) = "read" &&
         List.length args = 2 &&
         fst(dest_const(List.hd args)) = "events"
     with _ -> false) in
  DISCARD_ASSUMPTIONS_TAC(
    fun thm ->
      if is_events_hyp (concl thm) then false
      else
        let us = unbound_statevars_of_read [] (concl thm) in
        if us = [] || us = [v] then false
        else if not(mem v us) then true
        else true);;

(* ASM-aware version of DISCHARGE_MEMSAFE_TAC for loop bodies.
   Uses CONTAINED_ASM_TAC for contained_modulo proofs with symbolic bounds. *)
let DISCHARGE_MEMSAFE_ASM_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
    REPEAT CONJ_TAC THEN
    TRY(REPEAT ((DISJ1_TAC THEN CONTAINED_ASM_TAC) ORELSE DISJ2_TAC ORELSE
                CONTAINED_ASM_TAC) THEN NO_TAC);
    REWRITE_TAC[APPEND; APPEND_NIL] THEN
    FIRST_ASSUM ACCEPT_TAC];;



(* ------------------------------------------------------------------------- *)
(* MEMSAFE loop invariant (= CORRECT_LOOPINV + events-accumulator conjunct). *)
(* The register/memory tracking is needed to bound RAX (<=248) so the SIMD   *)
(* stores vmovdqu [rdi+rax*4] are provably in [res,1024).                    *)
(* ------------------------------------------------------------------------- *)
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

(* Scaffold proven to reach 5 subgoals (mirrors CORRECT_SCAFFOLD_TAC):
   WOP on (256<16i \/ 248<niblen) -> N>=2; ENSURES_WHILE_UP_TAC (N-1) (pc+52)(pc+52) MEMSAFE_LOOPINV.
   Subgoals: [G0 N-1<>0] [G1 init pc->pc+52, 11 steps] [G2 body i] [G3 back-edge] [G4 exit-block].
   TODO: prove G1..G4 mirroring CLEAN_BODY/MID_EXIT/EXIT_OFFSET/SCALAR_TAIL but tracking events
   via DISCHARGE_MEMSAFE_ASM_TAC / DISCHARGE_MEMSAFE_TAC + DISCARD_OLDSTATE_KEEP_EVENTS_TAC. *)

(* ------------------------------------------------------------------------- *)
(* VALIDATED in-session (2026-06-25): scaffold + G0 + G1 all close.          *)
(*   G0 (N-1<>0): REPEAT(FIRST_X_ASSUM(MP_TAC o check(~(N=0)/~(N=1)))) THEN  *)
(*                ARITH_TAC                                                   *)
(*   G1 (init pc->pc+52, 11 steps): mirror CORRECT G1 then                   *)
(*       EXISTS_TAC `[]:(uarch_event)list` THEN                              *)
(*       REWRITE_TAC[APPEND; memaccess_inbounds; ALL]                        *)
(*   => events-tracking discharge confirmed working.                         *)
(* REMAINING: G2 loop body (4 sub-iters, track events via                    *)
(*   DISCHARGE_MEMSAFE_ASM_TAC + DISCARD_OLDSTATE_KEEP_EVENTS_TAC),          *)
(*   G3 back-edge (refl), G4 exit-block (4 mid-exit cases + scalar tail).    *)
(*   Mirror the CORRECT decomposition (CLEAN_BODY / MID_EXIT_* / EXIT_OFFSET *)
(*   / SCALAR_TAIL) but carry the e_acc/memaccess_inbounds conjunct.         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* G2 BODY walk recipe (in progress 2026-06-25). After X_GEN_TAC i+STRIP:    *)
(*   ABBREV_TAC curlist = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist)     *)
(*   ABBREV_TAC curlen = LENGTH curlist                                      *)
(*   derive [16*i<=256 /\ niblen(16i)<=248] from hyp7 @ i (i<N-1<N), and     *)
(*   curlen<=248 via EXPAND curlen/curlist + LENGTH_REJ_SAMPLE_ETA4_BYTES.   *)
(*   ENSURES_INIT_TAC "s0".                                                  *)
(* KEY ISSUE: the precondition's (exists e_acc. read events s0 = APPEND...)  *)
(*   hyp must be X_CHOOSE'd to a concrete e0 BEFORE stepping, and preserved  *)
(*   across DISCARD via DISCARD_OLDSTATE_KEEP_EVENTS_TAC (NOT plain          *)
(*   DISCARD_OLDSTATE_TAC, which erases the events chain because POPCNT      *)
(*   operands transitively reference earlier memory reads).                  *)
(* The body = the CLEAN_BODY instruction walk (PREFIX_G_FULL + SI1..SI4)     *)
(*   but those tactics (a) assume the CORRECT goal shape (no events conjunct)*)
(*   so PREFIX_G_FULL_TAC fails with STRIP_TAC, and (b) call plain           *)
(*   DISCARD_OLDSTATE. => must walk manually: mirror each SIn_INTEGRATED's   *)
(*   X86_STEPS ranges but swap DISCARD_OLDSTATE_TAC ->                       *)
(*   DISCARD_OLDSTATE_KEEP_EVENTS_TAC, and after each vmovdqu store apply    *)
(*   DISCHARGE_MEMSAFE_ASM_TAC to extend memaccess_inbounds for that store.  *)
(*   JA-not-taken guards resolved exactly as in CORRECT (RESOLVE via         *)
(*   curlen<=248 / 16i bounds; RIP COND simplifies to pc+63 etc).            *)
(* Offsets (trimmed): head guards pc+52(CMP eax,248) pc+57(JA) pc+63(CMP     *)
(*   ecx,256) pc+69(JA) -> sub-iter1 from pc+75; mid-guards after si1/2/3 at *)
(*   pc+160/pc+216/pc+269 (CMP eax,248;JA, not-taken in body); back-edge JMP *)
(*   pc+309 -> pc+52. (Confirm exact via MLDSA_REJ_UNIFORM_ETA4_EXEC dump.)  *)
(* ------------------------------------------------------------------------- *)

(* CLEAN_BODY_MEMSAFE term = CLEAN_BODY's stmt + events conjunct in pre&post.
   Build via (after `let qvars,body=strip_forall(concl CLEAN_BODY); hyps_tm,ens=dest_imp body`):
     strip_comb ens -> [x86;pre;post;frame]; dest_abs pre/post -> sv,preb / sv2,postb;
     evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state)=APPEND e_acc (e:(uarch_event)list)
                /\ memaccess_inbounds e_acc [(buf:int64),272;(table:int64),2048] [(res:int64),1024]`;
     pre'=mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)); post' similarly;
     list_mk_forall(qvars@[`e:(uarch_event)list`], mk_imp(hyps_tm, list_mk_comb(ensc,[x86;pre';post';frame]))).
   KEY: MEMACCESS_INBOUNDS_APPEND splits memaccess_inbounds(APPEND e_body e0) into body+pre parts.
   Proof = walk body (mirror CLEAN_BODY step ranges) with DISCARD_OLDSTATE_KEEP_EVENTS_TAC and
   DISCHARGE_MEMSAFE_ASM_TAC after each store. Then loop applies CLEAN_BODY_MEMSAFE per block;
   mid-exit/scalar tail analogous. *)

(* Runnable builder for the strengthened CLEAN_BODY_MEMSAFE goal term.
   Load AFTER main file (so MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY is in scope). *)
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

(* PROOF TODO (manual walk; CLEAN_BODY_FULL_TAC does NOT apply to this shape):
   REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
   <X_CHOOSE the pre events hyp to e0> THEN
   <mirror PREFIX_G_FULL + SI1..SI4 step ranges, but use DISCARD_OLDSTATE_KEEP_EVENTS_TAC
    in place of any DISCARD_OLDSTATE_TAC, and after each vmovdqu store run DISCHARGE_MEMSAFE_ASM_TAC>
   THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN <value conjuncts: RAX/RCX final> THEN
   <events conjunct: EXISTS the accumulated APPEND, REWRITE[MEMACCESS_INBOUNDS_APPEND], split:
      body part via DISCHARGE_MEMSAFE_ASM_TAC, e0 part = the stripped hyp>. *)

(* VALIDATED walk prefix for clean_body_ms_tm (2026-06-25):
   g clean_body_ms_tm;;
   e(REPEAT GEN_TAC THEN STRIP_TAC THEN
     SUBGOAL_THEN `16 * i <= 256` ASSUME_TAC THENL
      [UNDISCH_TAC `16 * (i + 1) <= 272` THEN ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) <= 248` ASSUME_TAC THENL
      [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
       TRANS_TAC LE_TRANS `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i+1)) inlist):int16 list)` THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ARITH_TAC; ALL_TAC] THEN
     ENSURES_INIT_TAC "s0");;
   e(FIRST_X_ASSUM(X_CHOOSE_THEN `e0:(uarch_event)list` STRIP_ASSUME_TAC o check(fun th -> is_exists(concl th))));;
     -> gives hyps `read events s0 = APPEND e0 e` + `memaccess_inbounds e0 [buf,272;table,2048] [res,1024]`.
   e(MP_TAC(SPECL [`LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist):int32 list)`;`248`] JA_NOT_TAKEN_LE) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     VAL_INT64_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist):int32 list)` THEN
     X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2));;  (* head guard CMP+JA, not taken *)
   NEXT: resolve RIP s2 = word(pc+63) (mirror PREFIX_G_FULL), step (3--4) -> RIP pc+75, then
   walk SI1 (load chunk0 vpmovzxbw from buf -> 1 read event; store vmovdqu -> 1 write event),
   SI2/SI3/SI4 each: vmovq table read + vmovdqu res write. After EACH store run DISCHARGE_MEMSAFE_ASM_TAC.
   Use DISCARD_OLDSTATE_KEEP_EVENTS_TAC instead of DISCARD_OLDSTATE_TAC throughout.
   Mid-guards after si1/2/3 (CMP eax,248;JA) not-taken via JA_NOT_TAKEN_LE on the running acc<=248. *)

(* FINDING (2026-06-25): plain X86_STEPS_TAC (5--9) DISCARDS the events chain
   (events s9 hyp gone) because it calls DISCARD_OLDSTATE internally. So the body
   MUST be stepped either one-instruction-at-a-time with explicit
   DISCARD_OLDSTATE_KEEP_EVENTS_TAC between steps, OR find the X86_STEPS variant
   that preserves a named component. PR1014 steps singly around stores. The guard
   steps (1--4) are fine (no mem events); the loss starts once SIMD/mem ops run.
   Validated so far: walk reaches pc+75 (sub-iter 1 start, s4) with events tracked
   through the 2 head guards. NEXT: single-step 5.. with KEEP_EVENTS; after the
   vmovdqu store, DISCHARGE_MEMSAFE_ASM_TAC. *)

(* CORRECTION (2026-06-25): X86_STEPS_TAC DOES preserve events — they accumulate
   as a CONS chain (EventLoad/EventStore/EventJump) onto (APPEND e0 e). Confirmed:
   at s9 read events = CONS(EventLoad(buf+16i,16))(CONS EventJump..(CONS EventJump..(APPEND e0 e))).
   So NO special KEEP_EVENTS stepping needed — just walk the body with plain X86_STEPS,
   resolve the head guards (RIP s2=pc+63, s4=pc+75) and the 3 mid-guards
   (CMP eax,248;JA not-taken via JA_NOT_TAKEN_LE on running accept-count<=248) like
   CLEAN_BODY, reach back-edge JMP -> pc+52, then ENSURES_FINAL_STATE_TAC +
   value conjuncts (RAX_FINAL/RCX_FINAL style) + events conjunct:
     EXISTS_TAC the accumulated chain prepended to e0, then
     REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND]/DISCHARGE_MEMSAFE_ASM_TAC to prove each
     EventLoad(buf+16i,16) contained in (buf,272) [16i+16<=272], each table read
     contained in (table,2048) [index*8+8<=2048], each store contained in (res,1024)
     [4*acc+32<=1024 since acc<=248 => 4*248+32=1024], and the e0 tail via hyp 12.
   VALIDATED walk so far: reached s21 (sub-iter 1 done incl store, events tracked,
   counters advanced). Continue 22.. for si2/si3/si4 + mid-guards. *)

(* At s21: RIP=pc+152 (mid-guard 1 CMP eax,248), RCX=16i+4(zx). To resolve the
   mid-guard JA-not-taken, RAX must be bounded: RAX = word(niblen(16i+4)) <= 248.
   This requires the SAME accept-count folding as CLEAN_BODY (SI1_FOLD_V2 + the
   bitval/popcount lemmas) — i.e. the body MEMSAFE proof needs the full CLEAN_BODY
   fold machinery to bound RAX at each of the 3 mid-guards. So CLEAN_BODY_MEMSAFE
   genuinely re-does the CLEAN_BODY body proof + event discharge; budget accordingly.
   Mid-guard offsets (trimmed): pc+152 (after si1), then ~pc+? after si2/si3.
   Recommended: build CLEAN_BODY_MEMSAFE by editing copies of the SI*_INTEGRATED /
   MG*_NT tactics to (a) accept the events-strengthened goal shape and (b) append
   the events discharge, rather than walking raw instructions by hand. *)

(* ★★ MAJOR PROGRESS (2026-06-25): clean_body_ms_tm is ALMOST provable by the EXISTING
   CLEAN_BODY chain! Running:
     PREFIX_G_FULL_TAC THEN SI1_FOLD_V2 THEN SI2_INTEGRATED THEN SI3_INTEGRATED THEN
     SI4_INTEGRATED THEN RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16*i+16=16*(i+1)`]) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]
   walks the WHOLE body to s57 and leaves a 3-conjunct goal:
     [RAX-fold] /\ [RCX-fold] /\ [exists e_acc. read events s57 = APPEND e_acc e /\ memaccess_inbounds...]
   The first two close with the EXISTING RAX_FINAL_TAC / RCX_FINAL_TAC:
     e(CONJ_TAC THENL [RAX_FINAL_TAC; ALL_TAC]); e(CONJ_TAC THENL [RCX_FINAL_TAC; ALL_TAC]);
   => ONLY the events conjunct remains!
   ★ BLOCKER: the SI*_INTEGRATED tactics call plain DISCARD_OLDSTATE_TAC which DISCARDS the
   `read events s57` equation (only MAYCHANGE[...events...] s0 s57 survives). So at the events
   goal there's no events-chain hyp to discharge from.
   FIX OPTIONS: (a) rebuild SI1_FOLD_V2/SI2/3/4_INTEGRATED with DISCARD_OLDSTATE_KEEP_EVENTS_TAC
   substituted for DISCARD_OLDSTATE_TAC (mechanical edit of the .si*_integrated.ml assets), OR
   (b) prove a separate pure-events lemma for the body. (a) is the clear path: copy the 4 SI
   asset tactics to *_MS variants that keep events, then the body proof = the chain above +
   RAX_FINAL + RCX_FINAL + [EXISTS chain; REWRITE MEMACCESS_INBOUNDS_APPEND; DISCHARGE_MEMSAFE_ASM_TAC].
   This is MUCH smaller than re-deriving the fold — the value machinery is 100% reused. *)

(* WHY rebinding won't work: X86_STEPS_TAC -> X86_SINGLE_STEP_TAC -> DISCARD_OLDSTATE_TAC
   are captured by-value when SI*_INTEGRATED were defined (OCaml early binding). Rebinding
   the global DISCARD_OLDSTATE_TAC now does NOT change the frozen SI tactics. The events
   equation is discarded because EventLoad operands reference old-state memory reads, so
   DISCARD_OLDSTATE drops the `read events sN` hyp once those states are erased.
   => CLEANEST FIX: define KEEP_EVENTS stepping primitives and *_MS copies of the SI asset
   tactics that use them. Specifically build:
     let X86_SINGLE_STEP_KEEPEV_TAC th s = time(X86_VERBOSE_STEP_TAC th s) THEN
       DISCARD_OLDSTATE_KEEP_EVENTS_TAC s THEN CLARIFY_TAC;;
     let X86_STEPS_KEEPEV_TAC th ns = MAP_EVERY (X86_SINGLE_STEP_KEEPEV_TAC th) (statenames "s" ns);;
   then copy .si1_fold_v2/.si2_integrated/.si3_integrated/.si4_integrated/.prefix_g_full_tac
   to *_MS variants with X86_STEPS_TAC->X86_STEPS_KEEPEV_TAC (and X86_VSTEPS similarly if used).
   Body proof then = PREFIX_G_FULL_MS THEN SI1_FOLD_V2_MS THEN SI2/3/4_MS THEN
     RULE_ASSUM_TAC(REWRITE[16i+16=16(i+1)]) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL[RAX_FINAL_TAC; CONJ_TAC THENL[RCX_FINAL_TAC;
       <events: EXISTS the s57 chain minus e; REWRITE[MEMACCESS_INBOUNDS_APPEND];
        DISCHARGE_MEMSAFE_ASM_TAC per access + ACCEPT the e0 hyp]]].
   NOTE: also check X86_VSTEPS_TAC usage in SI tactics (VSTEPS = X86_VERBOSE_STEP, no discard,
   so those already keep events — only the plain X86_STEPS calls need swapping). *)

(* _MS attempt (2026-06-25): created .prefix_g_full_tac_ms / .si{2,3,4}_integrated_ms with
   X86_STEPS_TAC -> X86_STEPS_KEEPEV_TAC (def below) and tactic renamed *_MS. SI1_FOLD_V2
   reused as-is (no stepping). KEEPEV primitives:
     let X86_SINGLE_STEP_KEEPEV_TAC th s = time(X86_VERBOSE_STEP_TAC th s) THEN
       DISCARD_OLDSTATE_KEEP_EVENTS_TAC s THEN CLARIFY_TAC;;
     let X86_STEPS_KEEPEV_TAC th ns = MAP_EVERY (X86_SINGLE_STEP_KEEPEV_TAC th) (statenames "s" ns);;
   RESULT: PREFIX_G_FULL_MS_TAC FAILS with `FAIL: REFL_TAC`. Cause: keeping events means the
   `read events sN = CONS(EventJump(word(pc+K), <COND ...>)) ...` hyp embeds the raw RIP COND;
   PREFIX's guard-resolution SUBGOALs end `...DISCH_THEN SUBST1_TAC THEN REFL_TAC` and the kept
   events-COND breaks a downstream REFL (the COND isn't simplified in the events hyp).
   FIX: after each guard's RIP resolution, also rewrite the EventJump COND in the events hyp to
   the resolved target (mirror PR1014's cond_eq_clean: TRANS (SYM cond_th) clean_th then
   RULE_ASSUM_TAC(REWRITE_RULE[cond_eq_clean])). i.e. PREFIX_G_FULL_MS needs the Jump-COND cleanup
   applied to ASSUMPTIONS (incl events) at each of the head guards (s2->pc+63, s4->pc+75) and the
   3 mid-guards inside SI2/SI3/SI4. Add this cleanup into the _ms tactic copies. *)

(* ★ VALIDATED COND-cleanup recipe (2026-06-25) — fixes the REFL_TAC failure.
   After each guard's X86_STEPS_KEEPEV, the events hyp has
   `read events sN = CONS(EventJump(word(pc+K), <COND cond_c (pc+314) (pc+K)>)) ...`.
   Collapse it: extract cond_c from the events hyp's COND, then
     e(SUBGOAL_THEN `cond_c = F` ASSUME_TAC THENL
        [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
            then MP_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
         REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC]);
     e(RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `cond_c = F`; COND_CLAUSES]));
   (use `&256:int` for the pos/ecx guard). Confirmed: events s2 EventJump COND collapses to pc+63.
   So the _MS tactics need this 2-step cleanup inserted after EACH guard resolution
   (head guards s2,s4 + the 3 mid-guards in SI2/SI3/SI4). With that, the body proof completes:
   value via RAX_FINAL/RCX_FINAL, events via the now-COND-free CONS chain + MEMACCESS_INBOUNDS_APPEND
   + DISCHARGE_MEMSAFE_ASM_TAC. ALL mechanism now validated; remaining = wire the cleanup into the
   _ms tactic files + the per-access in-bounds discharge + replicate for mid-exit/scalar-tail. *)

(* ★ FULL forward path validated (2026-06-25): manually walked clean_body_ms with
   X86_STEPS_KEEPEV + per-guard COND-cleanup through BOTH head guards and into SI1.
   Confirmed event chain at s20 (RIP=pc+149, just before mid-guard 1 at pc+152):
     events s4  = CONS(EventJump(pc+75,pc+75))(CONS(EventJump(pc+63,pc+63))(APPEND e0 e))   [both guards collapsed]
     events s5  = CONS(EventLoad(buf+1*val(word(16i)),16)) (...)                            [SI1 vpmovzxbw load]
   So the load event is EventLoad(word_add buf (word(1*val(word(16*i)))), 16) — needs
   contained in (buf,272): since val(word(16i))=16i (16i<2^64) and 16i+16<=272 (16i<=256), holds.
   NEXT in walk = the popcnt/add updating RAX to acc1=niblen(16i+4), then mid-guard CMP eax,248
   at pc+152 — this is where SI1_FOLD_V2's accept-count fold is REQUIRED to get RAX<=248.
   => CONFIRMS the right build is: PREFIX_G_FULL_MS THEN SI1_FOLD_V2 THEN SI2/3/4_INTEGRATED_MS,
   with the COND-cleanup baked into the _MS tactic files at each guard. The cleanup to inject
   after each guard's X86_STEPS_KEEPEV resolution (events hyp sN):
     let cc = el 0 (snd(strip_comb (find_term is COND in events-sN-hyp))) in
     SUBGOAL_THEN `cc=F` ASSUME_TAC THENL [<MP the matching JA_NOT_TAKEN consequent>; ALL_TAC] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `cc=F`; COND_CLAUSES])
   (head guards use &248/&256; mid-guards use &248 on the running acc).
   STATUS: head-guard cleanup proven; SI1_FOLD_V2 reuse confirmed needed; remaining = bake
   cleanup into _MS files + finish SI fold reuse + events discharge + exit/tail + wrappers. *)

(* COND-cleanup tactic — WORKING version (v3, MESON-free, fast, valid):
   let MEMSAFE_COND_CLEANUP_TAC : tactic = fun (asl,w) ->
     let condapps = mapfilter (fun (_,th) -> let c=concl th in
       if can(find_term(fun t->t=`events`)) c
       then find_term(fun t-> try fst(dest_const(fst(strip_comb t)))="COND" && length(snd(strip_comb t))=3 with _->false) c
       else fail()) asl in
     match condapps with [] -> ALL_TAC (asl,w) | center::_ ->
       let cc = el 0 (snd(strip_comb center)) in
       (SUBGOAL_THEN (mk_eq(cc,`F`)) ASSUME_TAC THENL
         [REWRITE_TAC[] THEN
          FIRST_X_ASSUM(fun th -> if is_imp(concl th) &&
              (can(find_term((=)`&248:int`))(concl th) || can(find_term((=)`&256:int`))(concl th))
            then ACCEPT_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC); ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME (mk_eq(cc,`F`)); COND_CLAUSES])) (asl,w);;
   Standalone after head-guard-1: returns OK (fast, valid). MUST be defined BEFORE loadt'ing
   the _ms prefix (the prefix captures it by-value).
   REMAINING TUNING: PREFIX_G_FULL_MS still FAILs `mk_comb: types do not agree` — the cleanup
   `mk_eq(cc,F)` hits a non-bool `cc` at the 2nd head guard or s23 mid-guard (the find_term grabs
   a COND nested differently there). FIX: guard the extraction to only pick CONDs whose result
   type is :int64 (RIP targets) — filter `type_of center = `:int64`` and `type_of cc = `:bool``
   before building mk_eq; or pick the OUTERMOST COND in the most-recent events hyp only.
   Also: head-guard-1 worked when run as the very first cleanup; subsequent guards have multiple
   events hyps (s2,s3,s4 chains) so `condapps` has several — should target the LATEST state's. *)
