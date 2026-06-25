(* Sub-iter 4: from RIP=pc+268 (after SI3_RESOLVE) through the jmp pc+52 (loop back-edge).
   Mask = mask8d (R8 ushr24, byte 3 -> lanes 24-31, block3 = SUB_LIST(16i+12,4)). NO mid-guard
   (sub-iter 4 has no cmp/ja; ends jmp pc+52). Uses PREFIX4's lanes-24..31 maskbit + POPCNT_BYTE3. *)

(* SI4_PRE: fold RAX s47 -> word acc3, abbrev acc3, reabbrev mask8d, establish acc3<=248. *)
let SI4_PRE : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let pop_len3 = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) ->
          can(find_term(fun u->u=`mask8c:int64`))(concl th) | _ -> false) asms in
    let rax_red0 = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
          can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) asms in
    (* fold popcnt->block2len(SUB_LIST) then collapse the nest to word(acc2+block2len) *)
    RULE_ASSUM_TAC(REWRITE_RULE[pop_len3]) THEN RULE_ASSUM_TAC(REWRITE_RULE[rax_red0])) THEN
  ABBREV_TAC `acc3 = acc2 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (16*i+8,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8d = read R8 s47` THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 272`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=272 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd4 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_4) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let acc3_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_)) -> true | _ -> false) in
    let bnd4a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd4 in
    let bnd4b = REWRITE_RULE[acc1_def] bnd4a in
    let bnd4c = REWRITE_RULE[acc2_def] (REWRITE_RULE[ADD_ASSOC] bnd4b) in
    let bnd4d = REWRITE_RULE[acc3_def] (REWRITE_RULE[ADD_ASSOC] bnd4c) in
    ASSUME_TAC bnd4d THEN
    ASSUME_TAC (MATCH_MP (ARITH_RULE `acc3 + x <= 248 ==> acc3 <= 248`) bnd4d)) THEN
  VAL_INT64_TAC `acc3:num`;;

(* SI4_GATHER: vpsrldq (s48), movzbl capture (s49), gather, store-safe, counter+jmp -> RIP pc+52. *)
let SI4_GATHER : tactic =
  X86_VSTEPS_TAC EXEC (48--48) THEN
  X86_VERBOSE_STEP_TAC EXEC "s49" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s48 = mask8d:int64`]) THEN
  X86_VSTEPS_TAC EXEC (50--50) THEN REABBREV_TAC `tab4 = read YMM6 s50` THEN
  X86_VSTEPS_TAC EXEC (51--51) THEN REABBREV_TAC `pshuf4 = read YMM6 s51` THEN
  PURGE_STALE_STATES_TAC ["s50"] THEN
  X86_VSTEPS_TAC EXEC (52--52) THEN REABBREV_TAC `sx4 = read YMM1 s52` THEN
  X86_STEPS_TAC EXEC (53--57);;
