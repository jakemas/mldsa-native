(* ========================================================================= *)
(* DEV SCRATCH — sound CLEAN_BODY lemma replacing the UNSOUND BODY_CHEAT.     *)
(*                                                                           *)
(* NOT loaded by the main proof. This is the work-in-progress tactic for the *)
(* clean (non-mid-exiting) loop body iteration i -> i+1, valid for i+1 < N.  *)
(*                                                                           *)
(* WHY BODY_CHEAT IS UNSOUND: the asm has mid-iter `ja $248` exits after     *)
(* sub-iters 1,2,3. BODY_CHEAT claims RCX=16(i+1) on the i=N-1 -> pc2 path,  *)
(* but the final iteration can mid-exit with a PARTIAL RCX=16(N-1)+4k. For   *)
(* i+1 < N, NIBLEN_PREFIX_MONO + CLEAN_BLOCK_BOUNDS guarantee niblen at      *)
(* 16i, 16i+4, 16i+8, 16i+12 are all <= 248, so NO mid-exit fires: the       *)
(* iteration is clean and RCX=16(i+1) genuinely holds. CLEAN_BODY proves     *)
(* exactly that. The messy partial final iteration is absorbed by            *)
(* FINAL_BLOCK (pc+56 with loopinv(N-1) -> function return pc+406), so the   *)
(* partial state is never exposed at the loop-exit pc+318.                   *)
(* ========================================================================= *)

(* ---- VALIDATED PROLOGUE (interactively confirmed lands pc+110, s11) ----  *)
(* After MAP_EVERY X_GEN_TAC + the CLEAN_BODY hypotheses stripped:           *)
(*
  ABBREV_TAC `outlist0 = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist):int32 list` THEN
  ABBREV_TAC `outlen0 = LENGTH(outlist0:int32 list)` THEN
  SUBGOAL_THEN `outlen0 <= 248` ASSUME_TAC THENL
   [EXPAND_TAC "outlen0" THEN EXPAND_TAC "outlist0" THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    TRANS_TAC LE_TRANS
     `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i+1)) inlist):int16 list)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(outlist0:int32 list) = outlen0`]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
     can (find_term (fun t -> t = `RAX`)) (concl th) && is_conj(concl th))) THEN
  SUBGOAL_THEN `16 * i <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i + 1) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`buf:int64`;`272`;`inlist:byte list`;`i:num`;`s0:x86state`]
    SUB_LIST_16_BYTES_FROM_INT128) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i+1) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf (word(16*i)))) s0` THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(LAND_CONV NUM_REDUCE_CONV THENC REWRITE_CONV[]))) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN   (* -> pc+79, head guards passed *)
*)

(* ---- VALIDATED SIMD-SETUP STEPPING (per-op, no goal blowup) ----          *)
(* PURGE_STALE_STATES_TAC (define at top of dev session):
  let PURGE_STALE_STATES_TAC names =
    let refs_stale tm =
      let rec go t = match t with
        | Comb(Comb(Const("read",_),_),Var(nm,_)) when List.mem nm names -> true
        | Comb(a,b) -> go a || go b
        | Abs(_,b) -> go b
        | _ -> false in go tm in
    REPEAT(FIRST_X_ASSUM(fun th ->
      if refs_stale (concl th) then ALL_TAC else failwith "keep"));;

   Pattern PER vector op n (writing YMMk): VSTEP one, fold prior abbrevs into
   the new value eq, REABBREV, purge prior state. Confirmed s5..s8:
  X86_VSTEPS_TAC EXEC (5--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[<chunk0 mem-eq>; ARITH_RULE `1 * x = x`]) THEN
  REABBREV_TAC `f0load = read YMM0 s5` THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = f0load`]) THEN
  REABBREV_TAC `f1shl = read YMM1 s6` THEN PURGE_STALE_STATES_TAC ["s5"] THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s6 = f0load`;
                              ASSUME `read YMM1 s6 = f1shl`]) THEN
  REABBREV_TAC `f0or = read YMM0 s7` THEN PURGE_STALE_STATES_TAC ["s6"] THEN
  X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s7 = f0or`]) THEN
  REABBREV_TAC `f0nib = read YMM0 s8` THEN PURGE_STALE_STATES_TAC ["s7"] THEN
  X86_VSTEPS_TAC EXEC (9--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s8 = f0nib`]) THEN
  REABBREV_TAC `f1bnd = read YMM1 s9` THEN PURGE_STALE_STATES_TAC ["s8"] THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s9 = f0nib`]) THEN
  REABBREV_TAC `f0sub = read YMM0 s10` THEN PURGE_STALE_STATES_TAC ["s9"] THEN
  X86_VSTEPS_TAC EXEC (11--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM1 s10 = f1bnd`]) THEN
  REABBREV_TAC `mask8 = read R8 s11` THEN PURGE_STALE_STATES_TAC ["s10"]
  (* ^ VALIDATED end-to-end: lands pc+110 (first vextracti128), ~46 assums,
     registers abbreviated: f0load,f1shl,f0or,f0nib,f1bnd,f0sub,mask8.
     f0sub holds the (4-nibble) byte vector; mask8 the popcount mask. *)

  (* ---- SUB-ITER 1 (pc+110.. ) — VALIDATED through s13 ---- *)
  X86_VSTEPS_TAC EXEC (12--12) THEN          (* vextracti128 $0 f0sub -> xmm5 *)
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s11 = f0sub`]) THEN
  REABBREV_TAC `g0a = read YMM5 s12` THEN PURGE_STALE_STATES_TAC ["s11"] THEN
  X86_STEPS_TAC EXEC (13--13)                (* movzbl r8b->r10d : R10 = mask8 & 0xff *)
  (* mask8 (s11 R8) def = word_zx(word(sum 2^k * bitval(bit 7 (word_subword
     f1bnd (8k,8))))) — the vpmovmskb sign bits of the 32 bound-cmp lanes.
     g0a = low 128 bits of f0sub (the (4-nibble) bytes 0..15).
     NEXT: 14 vmovq (tab,r10,8)->xmm6 [table[mask8&0xff], the gather control];
           15 vpshufb xmm6,g0a->xmm6 [compact accepted (4-nibble) bytes to front];
           16 vpmovsxbd xmm6->ymm1 [8 bytes sx-> 8 int32];
           17 vmovdqu ymm1->(out,rax,4) [store 8 int32 at r[outlen0]].
     STORE VALUE to prove = REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3] (first 4-byte
     block) padded to 8 lanes; LENGTH advance = popcount(mask8&0xff)
     = LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]). Apply at store:
       PSHUFB_ACCEPTED_PREFIX_NUM (compaction=gather at ACC_IDX),
       VPMOVSXBD_LANE_EXTRACT (per-lane sx),
       ETA_GATHER / GATHER_FILTER_MAP_IDX_8 (gather=FILTER),
       WORD_SUB_4_NIBBLE_INT32_AS_SX (4-nibble byte sx = spec coeff).
     For value-correctness, FIRST establish f0sub & mask8 in spec form via
     SUBGOAL_THEN (lane lemmas VPSLLW_VPOR_VPAND_INT16_NIBBLES,
     VPSUBB_SIGN_BIT_LT_9, VMOVMSKB_BYTE_EQ_64) rather than leaving opaque. *)

  (* ---- SUB-ITER 1 store chain — VALIDATED end-to-end through s17 ---- *)
  X86_VSTEPS_TAC EXEC (14--14) THEN              (* vmovq (tab,r10,8)->ymm6 *)
  REABBREV_TAC `tab1 = read YMM6 s14` THEN PURGE_STALE_STATES_TAC ["s13"] THEN
  X86_VSTEPS_TAC EXEC (15--15) THEN              (* vpshufb ymm6,xmm5->ymm6 *)
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM5 s12 = g0a`;
                              ASSUME `read YMM6 s14 = tab1`]) THEN
  REABBREV_TAC `pshuf1 = read YMM6 s15` THEN PURGE_STALE_STATES_TAC ["s14"] THEN
  X86_VSTEPS_TAC EXEC (16--16) THEN              (* vpmovsxbd ymm6->ymm1 *)
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM6 s15 = pshuf1`]) THEN
  REABBREV_TAC `sx1 = read YMM1 s16` THEN PURGE_STALE_STATES_TAC ["s15"] THEN
  X86_STEPS_TAC EXEC (17--17)                    (* vmovdqu ymm1->(out,rax,4) STORE OK *)
  (* ^ store resolves via nonoverlapping; RIP past pc+136. ENTIRE sub-iter
     pipeline (load->nibble->bound/mask->extract->gather->compact->sx->store)
     now VALIDATED. Remaining CLEAN_BODY = mechanical: popcnt/add (instr 18-21,
     RAX_BOUND_AFTER_POPCNT_ADD_DIRECT), mid-guard ja (JA_NOT_TAKEN_LE +
     CLEAN_BLOCK_BOUNDS, no fire on clean iter), sub-iters 2/3/4 (same shape,
     g0 via vpsrldq/vextracti128 $1), then jmp pc+56, ENSURES_FINAL_STATE.
     For VALUE correctness use SUBGOAL spec-forms (not opaque REABBREV) +
     SUBITER store lemmas (ETA_GATHER, GATHER_FILTER_MAP_IDX_8,
     PSHUFB_ACCEPTED_PREFIX_NUM, VPMOVSXBD_LANE_EXTRACT, WORD_SUB_4_NIBBLE_*).
     Compose 4 via SUBITER_OUTLEN_STEP_4 + REJ_SAMPLE_ETA4_BYTES_16_AS_4. *)

(* ---- RECONNAISSANCE FINDINGS (sub-iter 1 fully mapped, s11->s21) ---- *)
(* Instruction layout (clean asm), one sub-iter = 10 instrs after setup:
     pc+110 s12 vextracti128 $0 f0sub->xmm5   (g0a = low128 of f0sub)
     pc+116 s13 movzbl r8b->r10d              (R10 = mask8 MOD 256)
     pc+   s14 vmovq (tab,r10,8)->xmm6        (tab1 = table[mask8&0xff])
     pc+   s15 vpshufb xmm6,xmm5->xmm6        (pshuf1 = compacted (4-nib) bytes)
     pc+   s16 vpmovsxbd xmm6->ymm1           (sx1 = 8 int32 sign-extend)
     pc+136 s17 vmovdqu ymm1->(out,rax,4)     STORE: writes bytes256 at
                                              word_add res (word(4*val(word outlen0)))
     pc+   s18 popcntl r10d->r9d              (cnt = popcount(mask8&0xff))
     pc+   s19 addl r9d,eax                   (ctr += cnt -> RAX)
     pc+   s20 shrl $8,r8d                    (mask8 >>= 8 for next sub-iter)
     pc+156 s21 addl $4,ecx                   (pos += 4: RCX = 16i+4)  [CONFIRMED]
     then cmp $248,eax ; ja scalar  (mid-iter guard 1)
   RCX at s21 = word_zx(word_add(word_zx(word(16*i)))(word 4)) = word(16i+4). [CONFIRMED]
   STORE lands via nonoverlapping at memory:>bytes256(word_add res(word(4*val(word outlen0)))). [CONFIRMED]

   KEY LESSON: opaque REABBREV + PURGE breaks the RAX/popcnt/mask8 chain (the
   value eqs get dropped with their source state). For CLEAN_BODY VALUE proof
   do NOT abbreviate mask8/f1bnd/f0sub opaquely; instead carry SUBGOAL spec-forms:
     - mask8 = word_zx(word_of_bits(\i. i<8 /\ bit(8i+7) <low64 of f1bnd>)) via
       VMOVMSKB_BYTE_EQ_64 (low lane) — gives the 8-bit accept mask of block.
     - f1bnd lane k (8k,8) = word_sub(nibble_k)(word 9): VPSUBB_SIGN_BIT_LT_9 ->
       bit 7 set iff nibble_k < 9. So mask bit k <=> nibble_k < 9 (ETA_GATHER hyp).
     - popcount(mask8&0xff) = LENGTH(FILTER(val<9) [n0..n7]) via POPCNT_EQ_LENGTH_FILTER_8
       = LENGTH(REJ_NIBBLES_ETA4 <4-byte block>) (8 nibbles of 4 bytes).
     - nibbles n_k from chunk0 bytes via VPSLLW_VPOR_VPAND_INT16_NIBBLES +
       VPMOVZXBW_LANE_EXTRACT (lo/hi nibble of each of the 4 block bytes).
   Then RAX after s19 = word(outlen0 + popcount) = word(LENGTH(REJ_SAMPLE_ETA4_BYTES
   (SUB_LIST(0,16i+4) inlist))) by SUBITER_OUTLEN_STEP_4; mid-guard via
   JA_NOT_TAKEN_LE + CLEAN_BLOCK_BOUNDS (niblen(16i+4)<=248 on clean iter). *)

(* TODO next session:
   - For VALUE correctness (not just shape), replace opaque REABBREV of the
     nibble/sub vectors with SUBGOAL_THEN `read YMMk sN = word(num_of_wordlist
     <nibbles/4-minus-nibble list of chunk0 bytes>)` proven via the lane
     lemmas (VPMOVZXBW_LANE_EXTRACT, VPSLLW_VPOR_VPAND_*, VPSUBB_SIGN_BIT_LT_9).
   - Then per sub-iter k=0..3: extract g0 (vextracti128/vpsrldq), movzbl mask
     low byte -> table index, vmovq table[idx], vpshufb, vpmovsxbd, vmovdqu
     store. At the store apply GATHER_FILTER_MAP_IDX_8 + PSHUFB_ACCEPTED_PREFIX_NUM
     + VPMOVSXBD_LANE_EXTRACT + WORD_SUB_4_NIBBLE_INT32_AS_SX + ETA_GATHER to
     show stored bytes = REJ_SAMPLE_ETA4_BYTES of the 4-byte block.
   - popcnt add: RAX_BOUND_AFTER_POPCNT_ADD_DIRECT. mid guard: JA_NOT_TAKEN_LE
     with CLEAN_BLOCK_BOUNDS (clean iter, no exit). Compose 4 sub-iters via
     SUBITER_OUTLEN_STEP_4 + REJ_SAMPLE_ETA4_BYTES_16_AS_4 + _STEP_16.
   - jmp back to pc+56; ENSURES_FINAL_STATE_TAC; outlen=16(i+1) shape. *)

(* ========================================================================= *)
(* COMPLETE LEMMA INVENTORY for CLEAN_BODY (all PROVEN & committed in main   *)
(* file as of 2026-06-10). The cheat-removal is now "execute the stepping",  *)
(* not "discover the math". Per-sub-iter k (block bytes b_{4k}..b_{4k+3}):   *)
(*                                                                           *)
(* VALUE (store = spec):  SUBITER_STORE_SPEC                                 *)
(*   `(!j. j<8 ==> (bit j m <=> EL j [nibbles] < 9)) /\                      *)
(*    (!j. j<8 ==> word_subword g (8j,8) = word_sub(word 4)(word(EL j ...))) *)
(*    ==> MAP word_sx (SUB_LIST(0,|ACC_IDX m|)(PSHUFB_OUT_LIST g m))         *)
(*        = REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3]`                             *)
(*   - discharge hyp1 (mask): VMOVMSKB_BYTE_EQ_64 + VPSUBB_SIGN_BIT_LT_9     *)
(*     applied to f1bnd lanes (f1bnd = vpsubb bound f0nib); bit j of low byte*)
(*     of mask8 = bit 7 (f1bnd byte j) = (nibble_j < 9).                     *)
(*   - discharge hyp2 (gather): f0sub byte j = word_sub(word 4)(f0nib byte j)*)
(*     and f0nib byte j = word(nibble_j) via VPSLLW_VPOR_VPAND_LOW/HIGH_BYTE *)
(*     + VPMOVZXBW_LANE_EXTRACT on chunk0 bytes.                             *)
(*   The pshufb output PSHUFB_OUT_LIST g m is the s2n simulator's            *)
(*   usimd16(f8) form; bridge via PSHUFB_OUT_BYTE (already used inside       *)
(*   PSHUFB_ACCEPTED_PREFIX). g0 = vextracti128/vpsrldq of f0sub; the table  *)
(*   index m = mask8&0xff (sub-iter 1), >>8 each subsequent.                 *)
(*                                                                           *)
(* MEMORY (store extends outlist):  BYTES_EQ_NUM_OF_WORDLIST_APPEND          *)
(*   read(mem:>bytes(res,4*(outlen0+len_k))) = num_of_wordlist(outlist0 ++   *)
(*   this_block) splits into the existing prefix (untouched) + the bytes256  *)
(*   store at res+4*outlen0. Needs dimindex(:32)*LENGTH this_block = 8*(...).*)
(*                                                                           *)
(* COUNT (RAX advance):  SUBITER_OUTLEN_STEP_4 + POPCNT_NIBBLES_4_BYTES_BRIDGE*)
(*   + RAX_BOUND_AFTER_POPCNT_ADD_DIRECT. After each popcnt+add,             *)
(*   RAX = word(outlen0 + sum of block lens so far) =                        *)
(*   word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16i+4k) inlist))).         *)
(*                                                                           *)
(* MID-GUARD (ja never fires on clean iter):  JA_NOT_TAKEN_LE +             *)
(*   CLEAN_BLOCK_BOUNDS. niblen(16i+4),(16i+8),(16i+12) all <= 248 from      *)
(*   niblen(16(i+1)) <= 248 (hyp) via NIBLEN_PREFIX_MONO. So RAX <= 248 at   *)
(*   each cmp; JA_NOT_TAKEN_LE gives RIP = next instr (no exit to pc+318).   *)
(*                                                                           *)
(* COMPOSE 4 sub-iters:  REJ_SAMPLE_ETA4_BYTES_16_AS_4                       *)
(*   REJ_SAMPLE_ETA4_BYTES [b0..b15] = APPEND of the 4 four-byte chunks.     *)
(*   With SUB_LIST(16i,16) inlist = [chunk0 bytes] (already in assumptions   *)
(*   as SUB_LIST_16_BYTES_FROM_INT128) and SUB_LIST(0,16(i+1)) =             *)
(*   APPEND (SUB_LIST(0,16i)) (SUB_LIST(16i,16)) via SUB_LIST_SPLIT +        *)
(*   REJ_SAMPLE_ETA4_BYTES_STEP_16, the 4 stores compose to the full         *)
(*   SUB_LIST(0,16(i+1)) outlist.                                            *)
(*                                                                           *)
(* LOOP CLOSE:  after sub-iter 4's add ecx,4 (RCX = 16i+16 = 16(i+1)) and    *)
(*   jmp pc+56, ENSURES_FINAL_STATE_TAC with the i+1 invariant.             *)
(*                                                                           *)
(* STEPPING METHOD (validated this session): NEVER plain X86_STEPS over the  *)
(* SIMD body (discards YMM/R8 values). Use per-op X86_VSTEPS + fold-stale-   *)
(* mem-to-chunk0 + REABBREV + PURGE_STALE_STATES_TAC. For VALUE correctness  *)
(* derive f0sub/mask8 SPEC forms via SUBGOAL_THEN (lane lemmas) rather than  *)
(* opaque REABBREV (opaque loses the structure AND breaks the RAX chain).    *)
(* Sub-iter instruction windows (clean asm): setup s1-s11 -> pc+110; then    *)
(* sub-iter 1 s12-s21 (vextracti128 $0 / movzbl / vmovq / vpshufb /          *)
(* vpmovsxbd / vmovdqu / popcnt / add / shr / add) -> pc+156 (cmp/ja);       *)
(* sub-iter 2 (vpsrldq $8); sub-iter 3 (vextracti128 $1); sub-iter 4         *)
(* (vpsrldq $8, no trailing ja, jmp pc+56).                                  *)
(* ========================================================================= *)

(* ========================================================================= *)
(* VALUE-LAYER COMPLETE (2026-06-10). All per-sub-iter SIMD-reduction lemmas  *)
(* proven & committed in the main file; file loads end-to-end. The gather and *)
(* mask hypotheses of SUBITER_STORE_SPEC compose by plain REWRITE:            *)
(*   gather byte j: REWRITE_TAC[F0SUB_BYTES; F0NIB_BYTES] gives               *)
(*     f0sub byte j = word_sub (word 4) (word (val(chunk0 byte j) MOD/DIV 16))*)
(*     = word_sub (word 4) (word nibble_j)  -- VERIFIED by REWRITE_CONV.       *)
(*   mask: REWRITE_TAC[F1BND_BYTES; F0NIB_BYTES] then MASK_ACCEPT gives        *)
(*     bit j (movzbl mask low byte) <=> nibble_j < 9 (nibbles<16 from F0NIB).  *)
(* CLEAN_BODY goal must carry YMM2/3/4 broadcast consts in pre+post and use    *)
(* body MAYCHANGE [ZMM0;ZMM1;ZMM5;ZMM6] (NOT ZMM2/3/4 -- they are preserved).  *)
(* Prologue (validated, lands pc+110 / s11 with YMM2/3/4 threaded, chunk0      *)
(* digitized, RAX=outlen0, RCX=16i): same as the prior prologue block above    *)
(* but with the YMM2/3/4 conjuncts in the invariant.                          *)
(* REMAINING: 4 sub-iters of X86_VSTEPS + REABBREV + (rewrite f0sub/mask via   *)
(* the byte-lemmas to discharge SUBITER_STORE_SPEC at each vmovdqu) + RAX/RCX  *)
(* tracking + mid-guards (JA_NOT_TAKEN_LE+CLEAN_BLOCK_BOUNDS) + compose via     *)
(* REJ_SAMPLE_ETA4_BYTES_16_AS_4 + jmp pc+56. Pure stepping, zero new math.    *)
(* ========================================================================= *)
