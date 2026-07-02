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

