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

(* PROGRESS 2026-06-25: with v3+typeguard cleanup embedded in _ms prefix, PREFIX_G_FULL_MS_TAC
   now runs 61s (was <2s) — head guards + SI1 byte-extraction + 4 f0sub/f1bnd folds all PASS.
   Failure advanced: REFL_TAC -> mk_comb -> `FAIL: tryfind`. The tryfind is in the post-SI1
   region — most likely the s23 mid-guard block (lines ~414-426): it does
     find blk0 (SUB_LIST(16*i,4) shape), find rax_red0 (word_zx(word_add..)), find ja (disj w/ word_sub)
   one of these `find`s now fails. Likely cause: the kept events hyps OR the cleanup's RULE_ASSUM
   rewrite altered/removed a hyp the find expects, OR an earlier guard's not-taken disjunction
   (which the cleanup's FIRST_X_ASSUM consumed via MP) is no longer present for the `ja` find at
   line 421. NOTE: cleanup uses FIRST_X_ASSUM(...ACCEPT...) which DELETES the matched not-taken
   consequent — but the s23 guard's `ja` find may need a DIFFERENT disjunction still in asl.
   NEXT: bisect by running prefix in chunks; check which `find` (blk0/rax_red0/ja) throws at s23.
   Possible fix: cleanup should MP_TAC+re-ASSUME (not consume) the consequent, or use ASSUME copy.
   STATE: head-guard COND cleanup fully working; SI1 fold reused intact; only post-SI1 find-shape
   interaction remains. _ms files committed. *)

(* TRYFIND LOCALIZED (2026-06-25): probe files /tmp/cs_s17.txt + /tmp/cs_c1821.txt confirm
   PREFIX_G_FULL_MS passes the SI1 store (s17) and counters (s18-21). The `tryfind` is in the
   SI1 accept-count FOLD region, lines ~355-410 of .prefix_g_full_tac_ms.ml — most likely the
   OCaml `find` at line 363-364 (`read R9 s21`) or the `maskbit` find at 384-388 (fragile nested
   bit/word_subword shape match). With KEEP_EVENTS the `read events s21` hyp + PURGE_STALE_STATES
   interaction is the suspect. These finds are pure value-fold logic (unrelated to events), so the
   issue is that PURGE_STALE_STATES_TAC ["s15"]/["s16"] (lines 345,347) behaves differently when
   events hyps reference purged states — it may drop or fail to retain the R9/maskbit hyp.
   NEXT: add probe before line 363 r9-find; if R9 s21 hyp missing, the KEEP_EVENTS purge dropped it
   -> need to ensure PURGE keeps R9. Likely fix: the events hyp at s21 references R9's popcount
   operand, so DISCARD/PURGE logic erases R9 too. Use a PURGE variant that keeps R9 (or run the
   fold BEFORE purging). This is the same class of issue as the events-discard but for value hyps. *)

(* s23 GUARD reached (2026-06-25): probe /tmp/cs_s23rip.txt confirms PREFIX_G_FULL_MS reaches the
   s23 mid-guard with `read RIP s23 = (if <not-taken-cond> then word(pc+314) else word(pc+163))`
   present (contains pc+163 AND read RIP s23) — so the s23 RIP resolution FIRST_ASSUM (line 452)
   matches fine. The earlier `tryfind` was BEFORE this probe was added; with the probe + the
   read-RIP-s23 restriction, the run now HANGS (>120s) at the s23 guard region (the
   REWRITE_TAC[GSYM blk0]/rax_red0/ja + REFL, or the MEMSAFE_COND_CLEANUP at 456). The s23 events
   COND is much bigger (full accept-count expression) so the cleanup's mk_eq(cc,F) + REWRITE over
   the large COND may be slow, OR a REWRITE loops. NEXT: (a) time the s23 cleanup separately;
   (b) the s23 EventJump COND condition is the accept-count `~(...248...) \/ ...=0` — the cleanup
   needs the matching not-taken consequent, which is the ASSUME'd `ja` (line 440), NOT a &248/&256
   imp-consequent — so the cleanup's FIRST_X_ASSUM(248/256 imp) FAILS to find it and the SUBGOAL
   cc=F can't close -> likely the hang/failure. FIX: the cleanup must also accept the already-proven
   `ja` disjunction form (not just the `248<2EXP32 ==> ...` imp form) for mid-guards. Generalize
   MEMSAFE_COND_CLEANUP_TAC to discharge cc=F from EITHER a `<imp> ==> ~disj` consequent OR a bare
   ASSUME'd `~disj`-equivalent (the mid-guard `ja`). *)

(* PROGRESS 2026-06-25 (cont): restricting the s23 `find ja` to the outlen0-disjunction
   (add `can(find_term(fun u->u=`outlen0:num`))(concl th)`) got PAST the s23 guard.
   Failure advanced tryfind -> `FAIL: CHOOSE`. The CHOOSE is in the post-s23 RAX-fold region
   (.prefix_g_full_tac_ms.ml ~lines 458+) — a value-fold step doing X_CHOOSE/CHOOSE on a witness
   that the kept events hyps perturb (likely an `?x. ...` the fold expects exactly one of, or the
   events `exists e_acc` precondition leftover got grabbed). NEXT: find the CHOOSE in lines 458-480
   and ensure it targets the value witness, not the events existential.
   FAILURE-POINT PROGRESSION (each fix advances): REFL_TAC -> mk_comb(cc-type guard) ->
   tryfind(s23 find ja restricted to outlen0) -> CHOOSE(post-s23 fold). The _MS adaptation is
   working; each guard/fold has a small kept-events interaction needing a targeted find-restriction.
   ~85% through PREFIX_G_FULL_MS. *)

(* CHOOSE LOCALIZED (2026-06-25): probes /tmp/cs_pre_clean23.txt + /tmp/cs_post_clean23.txt BOTH
   fired -> the s23 MEMSAFE_COND_CLEANUP_TAC COMPLETES. The `FAIL: CHOOSE` is in the FINAL
   RAX-fold of PREFIX_G_FULL_MS (.prefix_g_full_tac_ms.ml lines ~462-467):
     W(fun(asl,w)-> let pl=find(word_popcount = _) ; let rr=find(word_zx(word_add..)=_) ;
        RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]))
   The CHOOSE comes from RULE_ASSUM_TAC(REWRITE_RULE[snd pl/rr]) being applied to the kept events
   `exists e_acc. read events s = APPEND e_acc e /\ memaccess_inbounds...` precondition-style hyp
   (or the `read events sN = CONS(...)` chain): REWRITE_RULE descending under the existential /
   the CONS chain triggers a CHOOSE-based congruence failure. FIX OPTIONS: (a) before the fold,
   move the events hyps out of asl (e.g. wrap fold's RULE_ASSUM_TAC to SKIP events hyps — use a
   filtered RULE_ASSUM that leaves `read events`/`exists e_acc` hyps untouched), or (b) do the
   RAX-fold rewrite only on the RAX hyp (FIRST_X_ASSUM targeting `read RAX s23`) instead of
   RULE_ASSUM_TAC over ALL asms. (b) is cleaner: replace the blanket RULE_ASSUM_TAC with a
   targeted rewrite of just the RAX-read hyp.
   FAILURE PROGRESSION: REFL->mk_comb->tryfind->CHOOSE, now at the very LAST step of PREFIX_MS.
   Essentially PREFIX_G_FULL_MS is ~95% working — one targeted-rewrite fix from completing. *)

(* ★ FULL STRUCTURE MAPPED (2026-06-25) via .memsafe_driver.ml (self-contained: reload eta4 +
   build clean_body_ms_tm + load _MS tactics + test). The driver RAN end-to-end; RESULT:
   `FAIL: mk_comb: types do not agree` — now inside the SI2/3/4_MS chain, NOT the prefix.
   ROOT: each sub-iter's mid-guard is resolved by a SEPARATE tactic the _INTEGRATED tactic calls:
     SI2_INTEGRATED_MS ends with `SI2_MG_TAC THEN SI2_RESOLVE` (.si2_integrated_ms.ml line 70).
     SI2_MG_TAC (in .si2_midguard.ml/.si2_full.ml, loaded by main file) does the post-SI2 RIP-COND
     resolution — and like PREFIX's guards it breaks on the kept events EventJump COND (mk_comb /
     find-grabs-wrong-COND). SI3/SI4 analogous (SI3_MG_TAC, SI4's guard).
   => REMAINING FIX (uniform, mechanical): the mid-guard handlers SI2_MG_TAC/SI3_MG_TAC/SI4 guard
   each need (a) their RIP-resolution FIRST_ASSUM restricted with `can(find_term((=)`read RIP sN`))`,
   and (b) a MEMSAFE_COND_CLEANUP_TAC call after, EXACTLY like the PREFIX head/s23 guards already
   fixed. Since SI2_MG_TAC etc. are captured by-value inside SI2_INTEGRATED_MS, make _MS copies of
   the midguard tactics too (.si2_midguard_ms.ml etc.) with the same restrict+cleanup, and point
   the _ms integrated tactics at them.
   ALSO APPLIED: PREFIX final RAX-fold RULE_ASSUM_TAC now SKIPS events hyps (skip_ev filter) to
   avoid the CHOOSE — that fix is in .prefix_g_full_tac_ms.ml (committed); needs retest but the
   driver got PAST prefix into SI2, so the prefix CHOOSE fix likely WORKED (failure moved to SI2).
   DRIVER: .memsafe_driver.ml (loadt it in a fresh session; ~12min; logs /tmp/memsafe_drv.log).
   Needs tmp_memsafe_helpers.ml present in proofs dir (copy of /tmp/memsafe_helpers.ml). *)

(* PROGRESS 2026-06-25: created .si2_resolve_ms.ml + .si3_resolve_ms.ml (KEEPEV + restricted ifrip
   already present + MEMSAFE_COND_CLEANUP_TAC appended); repointed SI2_INTEGRATED_MS->SI2_RESOLVE_MS,
   SI3_INTEGRATED_MS->SI3_RESOLVE_MS. Driver loads resolve_ms before integrated_ms.
   RETEST: full body still `FAIL: mk_comb: types do not agree`, now reaching s24 — i.e. INSIDE
   SI2_INTEGRATED_MS's own body (steps 24-33 + the SUBITER_STORE_SPEC/g2 fold, .si2_integrated_ms.ml
   lines 13-68), BEFORE SI2_RESOLVE_MS. So the SI2 body fold itself has a find/term-construction that
   the kept events (EventStore at s29 from the vmovdqu) perturbs — likely the `find storef0` (line 42,
   `read (bytes256..) s29 = sx2`) or the SUBITER_STORE_SPEC ISPECL building an ill-typed g2/spec.
   NEXT: probe inside si2_integrated_ms around the store-fold (lines 40-58); check if a `find` grabs
   the events hyp or if PURGE/REABBREV over s29 with events present breaks. The fix is likely the same
   pattern: events hyps need to be excluded from a RULE_ASSUM/find in the SI2 body, OR the store-fold's
   find needs tightening. Prefix is DONE; SI2 body is the active front. */

(* PINPOINTED (2026-06-25): SI2 fails at the VERY FIRST step `X86_VSTEPS_TAC EXEC (24--24)`
   (markers si2_0/si2_acc1 fire, si2_v24 MISSING). `mk_comb: types do not agree`. NOT MOVZBL
   (that's later) and NOT ACC1_IDENT (fires before). The bare X86_VSTEPS step 24 fails with the
   LONG events CONS-chain present at s23 (SI1 added EventLoad+EventStore+EventJumps onto APPEND e0 e).
   The prefix used X86_VSTEPS with events fine (shorter chain), so it's the chain LENGTH/shape at s23
   that trips some conversion in X86_VERBOSE_STEP_TAC (a frame/read-over-write congruence builds an
   ill-typed comb on the events term). Tried MOVZBL_R10_CAPTURE_MS_TAC (events-skip) — not the cause.
   ★ STRATEGIC REASSESSMENT: threading the growing events CONS-chain through the value-fold body
   makes MANY internal conversions (X86_VSTEPS, RULE_ASSUM, COMPONENT_READ_OVER_WRITE) trip in turn.
   Each is a separate fix. BETTER ARCHITECTURE (PR1014-style, recommended for next session):
   DON'T keep events through the value walk. Instead:
     (a) prove clean_body VALUE part with the ORIGINAL tactics (events discarded) — already works,
     (b) SEPARATELY prove a pure-events lemma: from pc+52 to pc+52, read events grows by a bounded
         chain whose memaccess_inbounds holds — via a lean events-only walk (X86_STEPS_KEEPEV +
         DISCHARGE_MEMSAFE, ignoring all value folds), OR
     (c) use ENSURES_FRAME-style: the events conjunct is preserved across the body as an invariant
         if memaccess stays inbounds — but events DO change, so need the chain.
   Option (b) is cleanest: a separate minimal events walk that does NOT do value folding (so no
   RULE_ASSUM/COMPONENT conversions over events), just steps + DISCHARGE_MEMSAFE_ASM_TAC per access.
   The two ensures (value via CLEAN_BODY, events via the lean walk) compose since same step count.
   This avoids the whack-a-mole of patching every value-fold conversion. *)

(* LEAN-WALK TEST (2026-06-25): bulk `X86_STEPS_KEEPEV (1--20)` with NO value folds FAILS at
   `tryfind` — because the head guards (CMP/JA at steps 1-4) leave a COND RIP the simulator can't
   decode past without guard resolution. So even a "lean events-only" walk STILL needs:
   (a) head-guard RIP resolution (s2->pc+63, s4->pc+75) — needs the JA_NOT_TAKEN_LE bounds,
   (b) the 3 mid-guard RIP resolutions (after si1/2/3) — each needs RAX <= 248, i.e. the accept-count
       niblen fold (the HARD part of CLEAN_BODY). 
   CONCLUSION: events tracking and the accept-count value-fold are FUNDAMENTALLY COUPLED at the
   mid-guards (can't resolve the guard without the bound; can't keep events past the guard without
   resolving it). So the path forward IS the whack-a-mole: patch each value-fold conversion that
   trips on the events chain. Known trip points so far: X86_VSTEPS step 24 (SI2 first step, long
   events chain). The fix class: either (i) make the offending conversion events-aware (skip events
   hyps), or (ii) TEMPORARILY strip the events hyp to a side var before the value-fold and restore
   after (cleaner: ASSUME the events-eq under a fresh name, REMOVE it from asl during the fold,
   re-ASSUME after). Option (ii) generalizes: wrap each SI*_INTEGRATED_MS body so the events hyp is
   pulled out (UNDISCH/ABBREV) during value folding then put back — avoids ALL the per-conversion
   patches. RECOMMENDED NEXT: implement an "events-stash" wrapper:
     STASH = FIRST_X_ASSUM(LABEL_TAC "ev" o check is-events-eq);  ... value fold ...; restore.
   But events changes each step, so stash must happen per-step. Simplest robust: keep events ONLY
   across the actual mem-access instructions; for pure-register/SIMD steps use plain X86_STEPS
   (discard), then the events chain is only the access events. NEEDS DESIGN. *)

(* ★ EVENTS-STASH DESIGN (task #14, refined 2026-06-25) — the robust path.
   STEP→INSTR MAP for the loop body (pc+52, step k = kth instr):
     guards: 1(cmp eax) 2(ja) 3(cmp ecx) 4(ja); MEM ACCESSES at steps:
     5  = vpmovzxbw (rsi,rcx) load  -> EventLoad(buf+16i,16)
     14 = vmovq (rdx,r10,8) table   -> EventLoad(table+idx*8,8)   [sub-iter 1]
     17 = vmovdqu ymm1,(rdi,rax,4)  -> EventStore(res+4*acc,32)
     26,29 (sub-iter 2); 38,41 (sub-iter 3); 50,53 (sub-iter 4) — table read + store each.
     mid-guards: 22-23(after si1), 34-35(after si2), 46-47(after si3); back-edge jmp = 57.
   So mem-access step set = {5,14,17,26,29,38,41,50,53} (9 accesses: 1 load + 4 table + 4 store).
   PROBLEM CONFIRMED: keeping the events hyp in the goal while value-folds run trips MANY
   conversions (SI1 CHOOSE, SI2 VSTEPS-24 mk_comb, COMPONENT_READ_OVER_WRITE, RULE_ASSUM...).
   Patching each is whack-a-mole AND the interactive session degrades with redefs.
   ROBUST DESIGN: maintain the events relation as an OCaml `thm ref` OUTSIDE the goal asl, so
   discards never touch it. Mechanism:
     - Run the EXISTING CLEAN_BODY value proof UNCHANGED (events discarded; already works, ~153s).
       BUT capture, at each mem-access step, the local event-delta theorem
       `|- read events sK = CONS(EventX(addr,sz)) (read events s_{K-1})` BEFORE the discard.
     - This requires a custom step wrapper that, for the 9 access steps, snapshots the
       `read events sK = ...` assumption (via a hook) into a list ref, then proceeds normally.
     - After the body, fold the 9 deltas into `read events s57 = APPEND access_chain (read events s0)`
       by transitivity, prove `memaccess_inbounds access_chain [buf,272;table,2048][res,1024]`
       (each EventLoad/Store address in range via acc<=248 + 16i<=256 bounds), and discharge.
   ALTERNATIVE (simpler, try first): the value proof's stepping already produces the events hyp
   transiently. Insert a hook tactic AFTER each access step that does
     `FIRST_X_ASSUM(fun th -> if is `read events sK = CONS..` then (stash := th::!stash; ALL_TAC) ...)`
   — but stash-into-ref from inside a tactic is fine (side effect). Pure-register steps: let the
   normal discard drop their (no-op) events hyps. At end, chain the stashed deltas.
   This DECOUPLES events from value: value proof runs verbatim (CLEAN_BODY_FULL_TAC), events
   captured as a side-effect list, discharged at the end. NO value-fold patching needed.
   IMPLEMENTATION NOTE: the stash hook must run while `read events sK` is still in asl (right after
   the access step, before DISCARD_OLDSTATE). Since CLEAN_BODY uses X86_VSTEPS (no discard) for the
   SIMD steps and the events hyp persists within a sub-iter until PURGE_STALE_STATES, capture at
   sub-iter boundaries. Cleanest: a parallel pure-events ensures lemma proved with X86_STEPS_KEEPEV
   ONLY (no value tactics) BUT with guard-resolution supplied as ASSUMED bounds (curlen<=248 etc.
   passed in as hyps), so the events walk needs no fold — the bounds come free from the value proof
   run separately, then both compose via ENSURES conjunction (same trace). *)

(* ★★ DECISIVE (2026-06-25): in a FRESH clean session, PREFIX_G_FULL_MS_TAC alone now FAILS at
   CHOOSE (earlier same file passed prefix + reached SI2). And SI1_FOLD_V2 with events fails at
   CHOOSE. Conclusion: threading the events hyp THROUGH the value-fold tactics is FUNDAMENTALLY
   UNSTABLE — the same tactic passes/fails depending on subtle hyp ordering, and every value-fold
   conversion (RULE_ASSUM, REWRITE_RULE, X86_VSTEPS, COMPONENT_READ_OVER_WRITE, the store-fold's
   CHOOSE/MP chains) is a trip point on the events term. NOT a robust path.
   X86_STEPS_KEEPEV (1--4) also fails (tryfind) — guards need RIP resolved between steps.
   => MANDATORY DECOUPLED DESIGN (the ONLY robust path):
   Prove TWO separate ensures over the SAME pc+52->pc+52 transition, then conjoin:
     (A) VALUE: exactly MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY (already proven, events in its MAYCHANGE
         frame so events may change). UNCHANGED.
     (B) EVENTS: a NEW lemma CLEAN_BODY_EVENTS: same pre/post but tracking ONLY
         `exists e_acc. read events s = APPEND e_acc e /\ memaccess_inbounds e_acc R W`,
         with pre ALSO carrying the bound hyps needed for guards (curlen<=248, 16i<=256, and the
         per-subiter accept bounds acc1,acc2,acc3<=248 as EXTRA antecedents). Proof of (B): a walk
         that resolves guards (using the supplied bounds, NO niblen fold needed since bounds are
         hyps) + steps everything KEEPEV + at the 9 accesses extends memaccess_inbounds. Crucially
         (B) does NO value folding so no fold-conversion trips on events.
     Compose: ENSURES conjunction lemma `ensures s P Q1 C /\ ensures s P Q2 C ==> ensures s P (Q1/\Q2) C`
     (need to find/prove the single-ensures version — ENSURES_N_CONJ exists for ensures_n; for plain
     ensures use ENSURES_CONJ if present, else derive). The acc1/2/3<=248 bound hyps for (B) are
     produced by the value proof's WOP/scaffold context (niblen monotonicity) and threaded into the
     loop invariant, so the scaffold supplies them.
   THIS is task #14's real deliverable: CLEAN_BODY_EVENTS lemma + the bound antecedents + the
   ENSURES-conjoin. Stop trying to thread events through CLEAN_BODY's value tactics. *)

(* TOOLING SURVEY (2026-06-26): available in this s2n-bignum (eb5843f-ish, fork consttime):
   YES: ENSURES_N_CONJ, EVENTUALLY_N_CONJ, SAFE_META_EXISTS_TAC, DISCHARGE_MEMACCESS_INBOUNDS_TAC,
        mk_safety_spec, gen_mk_safety_spec, MEMACCESS_INBOUNDS_APPEND, allowed_vars_e/EXISTS_E2_TAC,
        the PR1014 DISCHARGE_MEMSAFE_* helpers (in tmp_memsafe_helpers.ml).
   NO:  PROVE_SAFETY_SPEC_TAC, DISCHARGE_SAFETY_PROPERTY_TAC (this rev predates them) — so the
        fully-automated pointwise-style PROVE_SAFETY_SPEC_TAC path is NOT available; must hand-build.
   ★ FINAL DESIGN for CLEAN_BODY_EVENTS (task #14/#15), the robust decoupled route:
     Plain `ensures` has NO postcondition-CONJ lemma; only `ensures_n` does (ENSURES_N_CONJ).
     So work in ensures_n:
       1. CLEAN_BODY is `ensures` — convert to ensures_n with its step count (use ENSURES_ENSURES_N
          / the X86 stepping already yields a step count; or re-prove CLEAN_BODY as ensures_n).
       2. Prove CLEAN_BODY_EVENTS as ensures_n (SAME step count, SAME pre/frame): track only the
          events conjunct. Pre carries EXTRA bound antecedents acc1,acc2,acc3<=248 (so guard
          resolution needs no niblen fold). Walk = X86 stepping (the ensures_n stepper) + per-guard
          RIP resolution from the bounds + DISCHARGE_MEMACCESS_INBOUNDS at the 9 accesses. NO value
          folds => no events-on-fold trips.
       3. Conjoin via ENSURES_N_CONJ -> ensures_n with (value /\ events) post; convert back to ensures.
     The acc1/2/3<=248 bounds: supplied by the scaffold loop-invariant (niblen monotonicity from the
     WOP hyp7 forall m<N). Thread them into CLEAN_BODY_EVENTS's antecedents.
   NB: the x86 step relation is functional/deterministic, but plain-ensures CONJ still needs the
   step-count alignment, hence ensures_n. This mirrors s2n-bignum's own constant-time architecture.
   This is the methodical path; the threaded-events _ms tactics are a dead end (unstable CHOOSE). *)

(* ★★★ DEFINITIVE ANALYSIS (2026-06-26) — MEMSAFE infrastructure gap.
   ensures_n LEMMAS exist (ENSURES_N_CONJ, ENSURES_ENSURES_N [needs x86 determinism hyp],
   ENSURES_N_ENSURES, ENSURES_N_TRANS, etc.) BUT:
   - No X86 ensures_n STEPPING tactic (X86_ENSURES_N_STEP_TAC absent) — can't drive an ensures_n
     proof of the body the way X86_STEPS drives ensures.
   - No PROVE_SAFETY_SPEC_TAC / DISCHARGE_SAFETY_PROPERTY_TAC (the automated constant-time path).
   - No obvious x86-determinism lemma by name to discharge ENSURES_ENSURES_N's antecedent.
   So BOTH viable routes need infrastructure not present in this s2n-bignum rev (eb5843f-era):
     (a) threaded-events value walk  -> UNSTABLE (CHOOSE flakiness), dead end;
     (b) decoupled ensures_n conjoin -> needs an X86 ensures_n stepper + determinism, i.e. build
         a chunk of the constant-time tactic layer ourselves.
   RECOMMENDATION (for the human / next effort): bump s2n-bignum to a rev that ships the full
   constant-time tooling (PROVE_SAFETY_SPEC_TAC + DISCHARGE_SAFETY_PROPERTY_TAC + X86 ensures_n
   steppers), add a `mldsa_rej_uniform_eta4` entry to subroutine_signatures.ml, then the MEMSAFE
   proof is ~the pointwise pattern: mk_safety_spec + PROVE_SAFETY_SPEC_TAC (small, mostly automated).
   The pointwise_avx2_asm.ml MEMSAFE proof (committed, cheat-free) is the exact template once that
   tooling is present. Until then, the eta4 MEMSAFE stubs remain CHEAT_TAC (deferred, as originally
   scoped). CORRECT is fully cheat-free and nix-building — that milestone stands. *)

(* ★★ DECISIVE (2026-06-26): the AUTOMATED mk_safety_spec + PROVE_SAFETY_SPEC_TAC approach
   CANNOT prove eta4 MEMSAFE. Two hard blocks:
   1. The shimmed X86_SINGLE_STEP_TAC (eta4 main file's, knows r8b) DOES fix the register_size r8b
      decode failure — pass it via GEN_PROVE_SAFETY_SPEC_TAC (not the vanilla PROVE_SAFETY_SPEC_TAC
      which uses the unshimmed X86_SINGLE_STEP_TAC). With it, stepping reaches s28 (was s24).
      NOTE: eb5843f's REGISTER_ALIASES does NOT include r8b..r15b/r8w..r15w (only al..dil), so even
      the build's vanilla OPERAND_SIZE_CONV fails on r8b — the eta4 main-file shim is REQUIRED.
   2. FATAL: at s28 (sub-iter-1 store vmovdqu [rdi+rax*4]) -> `could not prove that updates will not
      modify the program code`. The store offset is DATA-DEPENDENT (rax = accept count); proving it
      doesn't hit code needs rax<=248. PROVE_SAFETY_SPEC_TAC does PURE LINEAR symbolic stepping and
      (a) has no accept-count bound, (b) mk_safety_spec produces a FLAT (loop-free) spec pc->pc+len,
      so it can't even handle eta4's loop (jmp back-edge). It's designed for STRAIGHT-LINE code
      (pointwise/ntt have fixed-offset stores, no data-dependent loop).
   => CONCLUSION: eta4 MEMSAFE REQUIRES the manual loop-aware proof (scaffold + body + exit-block,
   events-strengthened), and the events tracking FUNDAMENTALLY couples with the accept-count value
   invariant at both the mid-guards AND the stores (store-noncode needs rax<=248). No automated or
   lean shortcut exists. Revert to tasks #14-20 manual plan with the events-stash/decoupled design.
   The mk_safety_spec machinery + the eta4 sig entry remain useful for DERIVING the final SAFE-shaped
   spec from the proven core MEMSAFE (the spec SHAPE is auto-generated correctly). *)

(* ★★★ DEFINITIVE ARCHITECTURE (2026-06-26) after exhausting all approaches:
   The events hyp in the goal interferes with EVERY sub-iter's value-fold:
     - SI1_FOLD_V2: CHOOSE failure (SUBITER_FOLD_STEP MP does existential reasoning over asl)
     - SI2 step-24 X86_VSTEPS: mk_comb (verbose stepper conv builds ill-typed term on events CONS)
     - COMPONENT_READ_OVER_WRITE / RULE_ASSUM: trip on events term
   Patching each is endless whack-a-mole AND the interactive session degrades with redefs.
   Automated mk_safety_spec/PROVE_SAFETY_SPEC_TAC: RULED OUT (linear-only, no loop, data-dep store
   needs rax<=248; but the SHIMMED X86_SINGLE_STEP_TAC fixes r8b decode and reaches s28 before the
   store-noncode block).
   THE ONLY ROBUST PATH = FULLY DECOUPLE events from value:
   (1) Prove CLEAN_BODY value part with the ORIGINAL CLEAN_BODY_FULL_TAC (events discarded) — works,
       ~153s, gives `ensures ... (BUTLAST tmc) [pc+52 -> pc+52, value post] (MAYCHANGE incl events)`.
   (2) Prove a SEPARATE pure-events body lemma:
       `ensures ... (\s. pre-events-state) (\s. exists e2. events = APPEND e2 e0 /\ memaccess_inbounds e2 ..)
        (MAYCHANGE ...)` BY a walk that uses X86_STEPS_KEEPEV ONLY (no value folds) and supplies the
       guard bounds (curlen<=248, acc1/2/3<=248, 16i<=256) AS HYPOTHESES (passed in). The events walk
       needs guard RIP-resolution (uses bounds) + per-access DISCHARGE_MEMSAFE but NO accept-count
       fold and NO store value-fold — so NO CHOOSE/mk_comb interference.
       KEY: the store-noncode check in the events walk also needs rax<=248 — supply as hyp; the
       events walk's stores are proven inbounds via the same bound.
   (3) COMPOSE (1)+(2): both are `ensures` over the SAME pre/trace with compatible MAYCHANGE; use
       ENSURES_CONJ-style (or prove the conjoined postcondition by running BOTH ensures — they share
       the step sequence). The combined post = value-post /\ events-post = clean_body_ms_tm's post.
   The bounds (2) needs come FROM (1)'s invariant / the scaffold (which has niblen<=248 per i).
   This is the events-stash idea done right: value and events proven SEPARATELY, never in one goal.
   ESTIMATE: building the pure-events walk lemma + composition = the bulk of remaining work,
   comparable to ~1/3 of the CLEAN_BODY effort (no folds, just steps+guards+discharge). Tractable
   but multi-hour. Do it file-based via .memsafe_setup.ml + a dedicated .events_body.ml, NOT
   interactively (session degrades). *)

(* CIRCULARITY (2026-06-26): the pure-events walk does NOT escape the value coupling. Even with
   acc_k<=248 bounds supplied as hyps, the mid-guard `cmp eax,248` resolution needs rax = word(acc_k)
   at that point, but the events walk computes rax as the raw popcount-add expression — rewriting it
   to word(acc_k) IS the SI fold. So events tracking through the loop body inherently requires the
   value fold at the guards/stores. NO clean decoupling exists.
   => The actual path IS the whack-a-mole: track events alongside the value proof, patch each
   value-fold/events-hyp interference. Prefix already fully passes. Remaining: SI1 CHOOSE + SI2
   mk_comb + (likely) SI3/SI4 similar. Fix at source: make the specific failing operations
   events-hyp-aware (skip/stash the events eq during that op). The interference points are NARROW
   (one op per sub-iter fold) — finite, not infinite. Resume there with a FRESH session (setup driver)
   to avoid the degraded-redef state. *)
