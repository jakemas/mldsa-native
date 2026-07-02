(* ========================================================================= *)
(* CLEAN_BLOCK (2026-06-24): the SIMD 16-byte block body pc+52 -> pc+52,        *)
(* WITHOUT the `~(N=0)` and `i+1<N` hyps of clean_body_tm (the gather tactics    *)
(* never use them), and with the relaxed bound `16*(i+1)<=272` (so it covers     *)
(* BOTH clean blocks AND the exit block at i=N-1 where 16*N=272). Proved by the   *)
(* same CLEAN_BODY_FULL_TAC. This is the asset for the exit-block OFFSET arm:     *)
(* CLEAN_BLOCK @ i=N-1 takes pc+52/pos=16(N-1) -> pc+52/pos=16N, then the head    *)
(* guard cmp ecx,256 fires (16N=272>256) -> pc+314, then SCALAR_TAIL_AT_P@272.    *)
(* Load after the full CLEAN_BODY chain (needs CLEAN_BODY_FULL_TAC + clean_body_tm). *)
(* ========================================================================= *)
let clean_block_tm =
  let hs = conjuncts(fst(dest_imp(snd(strip_forall clean_body_tm)))) in
  let hs' = filter (fun h -> h <> `~(N = 0)` && h <> `i + 1 < N`) hs in
  list_mk_forall(fst(strip_forall clean_body_tm),
    mk_imp(list_mk_conj hs', snd(dest_imp(snd(strip_forall clean_body_tm)))));;

let CLEAN_BLOCK = prove(clean_block_tm, CLEAN_BODY_FULL_TAC);;
