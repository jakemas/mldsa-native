# Handoff prompt — finish the x86_64 ML-DSA `rej_uniform_eta4` HOL Light proof

Paste everything below into the new session.

---

You are continuing a HOL Light verification of the x86_64 AVX2 `mldsa_rej_uniform_eta4`
rejection-sampling routine. The hard part is **done**; the remaining work is well-scoped.
Read your memory files first (`MEMORY.md` index, then especially
`eta4-subiter2-r9-unblocked.md` and `hol-load-cwd-and-loaded-files.md`) — they contain the
detailed recipes and gotchas. Do NOT re-derive what's already proven.

## Environment & how to drive it

- HOL Light runs via the **`hol-light` MCP server** (tools: `mcp__hol-light__eval`,
  `goal_state`, `hol_restart`, `hol_status`, etc.). Call `hol_help()` for the tactic guide.
- Config: `/home/ubuntu/hol-light/mcp/hol-mcp.toml`, checkpoint = **`x86-mldsa-eta2`**,
  timeout 1200s, **`max_output_chars` truncates eval output to ~4000 chars showing the HEAD** —
  so dump big goals/asms to `/tmp/*.txt` with `open_out`/`output_string` and `Read` them, never
  print full goals. Use `(e(TAC);())` style and `W(fun (asl,w) -> ...)` to inspect state.
- Working dir for proofs: `/home/ubuntu/mldsa-native/proofs/hol_light/x86_64/proofs/`.
  Reusable proof artifacts are **dotfiles** (`.prefix_g_full_tac.ml`, `.si*_*.ml`, etc.) there.
- Git: commit validated milestones (the user wants steady commits). Branch is
  `x86-rej-eta4-eta2-hol-light`. End commit messages with the Co-Authored-By line.

## CRITICAL: the checkpoint does NOT contain the eta4 file — load it every fresh session

The `x86-mldsa-eta2` checkpoint has s2n-bignum + mldsa base loaded, but NOT
`rej_uniform_eta4_avx2_asm.ml`. Two gotchas bite every reload (see
`hol-load-cwd-and-loaded-files.md`):

1. **CWD** must be the proofs dir or `define_assert_from_elf` can't find the `.o`.
2. **`loaded_files`** dedup makes `loadt` silently no-op the file.

Fresh-session load recipe (run via `mcp__hol-light__eval`):
```ocaml
let contains sub s = let n=String.length sub and m=String.length s in
  let rec go i = i+n<=m && (String.sub s i n = sub || go (i+1)) in go 0;;
Sys.chdir "/home/ubuntu/mldsa-native/proofs/hol_light";;
loaded_files := List.filter (fun (s,_) -> not (contains "rej_uniform_eta4" s)) (!loaded_files);;
loadt "/home/ubuntu/mldsa-native/proofs/hol_light/x86_64/proofs/rej_uniform_eta4_avx2_asm.ml";;  (* ~440s *)
```
Then load `clean_body_build.ml` lines 1–330 (defs only: EXEC, clean_body_tm, SUBITER_FOLD_STEP,
LEN_RECONCILE, LACC8, maskbit_tgt, pf_target, MASKBIT_PF_TAC) — there's a `Printf.printf
"ABOUT_TO_PROVE"` marker at line ~330; `head -330 clean_body_build.ml > /tmp/cbb_defs.ml` then
`loadt`. Then load the artifact dotfiles in this dependency order:
`.subiter_k_lemmas .subiter_byte23_lemmas .maskbit_tgt_tac .tab1_teq_tac .pf_target_proof
.prefix_g_full_tac .si1_fold_v2 .maskbit_tgt_2_tac .si2_fold_pieces .si2_fold_complete .si2_full
.si2_integrated .si3_full .si3_fold_pieces .si3_integrated .si4_full .si4_fold_pieces
.si4_integrated .acc_full_len .rax_final .rcx_final .clean_body_full .scalar_tail_lemmas`.
(Re-deriving the whole CLEAN_BODY via `CLEAN_BODY_FULL_TAC` takes ~153s; only do it if you need
the theorem in-session.)

OPTIONAL (recommended): once the eta4 file + dotfiles are loaded, make a NEW checkpoint so future
sessions skip the 440s reload:
`python3 /home/ubuntu/hol-light/mcp/make_checkpoint.py --name x86-mldsa-eta4` (note: it evaluates
single expressions; multi-phrase setup must be in a file loaded via `needs`). Then point
`hol-mcp.toml`'s `checkpoint =` at it.

## The target & the binary

- Goal theorem: `MLDSA_REJ_UNIFORM_ETA4_CORRECT` (and `_BOUND`, `_SUBROUTINE_CORRECT`, the two
  `_MEMSAFE`, IBT wrappers) in `rej_uniform_eta4_avx2_asm.ml`.
- **The verified binary is the PRODUCTION 248/mid-guard variant** (decided + confirmed: the proof
  `.o` and `mldsa/src/native/x86_64/src/rej_uniform_eta4_avx2_asm.S` both have threshold 248 with
  mid-iteration `cmpl $248,ctr; ja scalar` after sub-iters 1/2/3). The proof-dir `.S` was synced to
  match. `LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc) = 407`. Loop head pc+56, scalar tail pc+318,
  function end pc+~406/407.

## What is DONE (proven cheat-free, committed)

- **`MLDSA_REJUNIFORM_ETA4_CLEAN_BODY`** — the entire SIMD loop body pc+56→pc+56 for one full
  16-byte iteration (all 4 sub-iters: gather + GENUINE table-load bridge + store-fold + counters +
  3 mid-guards-not-taken + final RAX/RCX), hyps=0, **no CHEAT**. This was the hard research gap.
  Tactic `CLEAN_BODY_FULL_TAC` (`.clean_body_full.ml`). Hypotheses include `i+1<N`,
  `16*(i+1)<=256`, `niblen(SUB_LIST(0,16*(i+1)))<=248`, and YMM2/3/4 = the 3 broadcast constants.
- **`CONTINUE_TAC`** (`.body_wiring.ml`) — discharges the loop-body obligation for the *continue*
  case (i+1<N) via CLEAN_BODY + `ENSURES_FRAME_SUBSUMED` (CLEAN_BODY's `[ZMM0;1;5;6]` frame
  subsumed by the loop's `[ZMM0..6]`).
- **`INTERMED_OUTLEN_LE`** (`.exit_iter_design.ml`) — for clean iterations no mid-guard fires
  (intermediate sub-iter outlens ≤248).
- **scalar-tail spec lemmas** (`.scalar_tail_lemmas.ml`): `SUB_LIST_1_EL`, `SUB_LIST_STEP_1`,
  `REJ_SAMPLE_STEP_1`, `LENGTH_REJ_SAMPLE_STEP_1` (per-byte = 2-nibble REJ_SAMPLE extension).

## What is LEFT (4 `CHEAT_TAC`s in the file)

1. **`MLDSA_REJ_UNIFORM_ETA4_BODY_CHEAT`** (line ~4633) — its stated postcond `RCX=16(i+1)`,
   `RAX=outlen(16(i+1))` is **WRONG for the last iteration**: with mid-guards, the SIMD loop can
   exit to the scalar tail mid-iteration at `pos=16i+4k` with a partial count. **The fix is a
   re-decomposition of `CORRECT`'s Phase 2**: run `ENSURES_WHILE_UP2` for **N−1** clean iterations
   (each = `CONTINUE_TAC`/CLEAN_BODY — valid by INTERMED_OUTLEN_LE), then a **combined tail**
   (the last SIMD iteration, which may mid-exit, + the scalar loop) from pc+56 → pc+407. Also
   strengthen the loop invariant (CORRECT line ~4796) with YMM2/3/4 and re-prove the preamble
   subgoal (the 3 `vpbroadcastd` at preamble instrs set them). The per-sub-iter fold tactics
   (`SI1_FOLD_V2`, `SI2/3/4_INTEGRATED`) are reusable building blocks for the last-iteration
   sub-iters; the NEW work is the guard-TAKEN branches.
2. **`MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_CHEAT`** (line ~4685) — the pc+318 byte-at-a-time loop.
   Decode: pc+318 `cmp eax,256;jnb done`; pc+325 `cmp ecx,272;jnb done`; load byte rsi+rcx, inc
   ecx; low nibble `&15`, `cmp 9;jnb skip`, store `4-nibble` at rdi+4*rax, inc eax; `cmp
   eax,256;jnb`; high nibble `>>4&15` same; `jmp pc+318`. Own nested `ENSURES_WHILE_UP`/`UP2`,
   capped output `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist)`. Use `.scalar_tail_lemmas.ml`
   (per-byte step) for the invariant. Template: PR1014 `SCALAR_BODY_LEMMA` in
   `/home/ubuntu/mldsa-native-pr1014/proofs/hol_light/x86_64/proofs/rej_uniform_avx2_asm.ml`
   (different spec, same loop shape, COND postcond `if i+1<K then pc+181 else pc+242`).
3. **`MLDSA_REJ_UNIFORM_ETA4_MEMSAFE`** + **`..._NOIBT_SUBROUTINE_MEMSAFE`** (lines ~4972, ~5000)
   — re-run the whole program tracking `memaccess_inbounds`. Toolkit template: PR1014's
   `DISCHARGE_MEMSAFE_ASM_TAC` / `MEMSAFE_ARITH_TAC` / `MEMSAFE_BITVAL_TAC`. Then the IBT-wrapped
   `_SUBROUTINE_CORRECT`/`_SUBROUTINE_MEMSAFE` via `ADD_IBT_RULE` (currently commented out).

## Oracle / templates

- **The complete aarch64 eta4 proof** (`../../aarch64/proofs/rej_uniform_eta4_aarch64_asm.ml`, 0
  cheats) is the ALGORITHM oracle — same WOP `N`, same `REJ_NIBBLES_ETA4`/`REJ_SAMPLE_ETA4_BYTES`
  spec, same capped `MIN 256` post-loop reasoning. BUT its loop shape does NOT transfer: aarch64
  processes 8 nibbles with a SINGLE guard (no mid-iteration exits), so the x86 mid-guard
  decomposition (item 1) is genuinely x86-specific.
- **PR1014** (`/home/ubuntu/mldsa-native-pr1014/...rej_uniform_avx2_asm.ml`, 0 cheats) is the x86
  ISA-stepping template for the scalar loop and MEMSAFE toolkit.

## Suggested order

Start with **SCALAR_TAIL** (self-contained, removes a cheat, foundational lemmas already in
`.scalar_tail_lemmas.ml`), then the **BODY re-decomposition** (item 1, the gating item for
CORRECT), then **MEMSAFE + IBT**. Verify each as a real `prove(...)` with hyps=0 / no CHEAT before
committing. Keep the user's working style: dump-don't-print, commit validated milestones, don't
overclaim — `MLDSA_REJ_UNIFORM_ETA4_CORRECT` is NOT cheat-free until all 4 cheats are gone.
