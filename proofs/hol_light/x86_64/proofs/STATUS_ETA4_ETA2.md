# ML-DSA eta4/eta2 x86_64 AVX2 — work-in-progress snapshot

This is a **draft / WIP snapshot** of the ML-DSA rej_uniform_eta4 and
rej_uniform_eta2 AVX2 assembly implementations together with their
HOL Light proofs. It is not ready for merge; it is parked here so the
state is reviewable and not lost between sessions.

## What lives where

### Production assembly (compiled into the library)

| Path | Notes |
| --- | --- |
| `mldsa/src/native/x86_64/src/rej_uniform_eta4_avx2_asm.S` | Clean, hand-written. Mirrors `eta2_avx2_asm.S` style. ~8700 cycles for `poly_uniform_eta_4x` benchmark. KATs pass. |
| `mldsa/src/native/x86_64/src/rej_uniform_eta2_avx2_asm.S` | Clean, hand-written. Existing PR1014/PR1151 style. |
| `mldsa/src/native/x86_64/meta.h` | Wires up `mld_rej_uniform_eta4_avx2_asm(r, buf, table)`. |
| `dev/x86_64/src/rej_uniform_eta{2,4}_avx2_asm.S` | Mirrored copies under `dev/` (used by `scripts/autogen` for HOL-Light artifact regeneration). |

### Variants (kept around for comparison, not compiled by default)

| Path | Notes |
| --- | --- |
| `dev/x86_64/variants/rej_uniform_eta4_avx2_asm_clean.S` | The clean version currently in production. |
| `dev/x86_64/variants/rej_uniform_eta4_avx2_asm_gcc_derived.S` | Software-pipelined variant derived from `gcc -O3` on the C intrinsics. ~8520 cycles (~2% faster). Kept for reference; *not* the one being formally verified. |

### HOL Light proofs

| Path | Notes |
| --- | --- |
| `proofs/hol_light/x86_64/proofs/rej_uniform_eta4_avx2_asm.ml` | **In progress.** Bytecode block freshly imported from the clean asm via `save_literal_from_elf`. |
| `proofs/hol_light/x86_64/proofs/rej_uniform_eta2_avx2_asm.ml` | Skeleton only; `MLDSA_REJ_UNIFORM_ETA2_CORRECT`/`MEMSAFE` admitted with `CHEAT_TAC`. |
| `proofs/hol_light/x86_64/proofs/mldsa_rej_uniform_table.ml` | Shared 256×8 byte lookup table definition. |
| `proofs/hol_light/x86_64/mldsa/rej_uniform_eta4_avx2_asm.S` | Symlink/copy used by HOL-Light build (matches the production `.S`). |
| `proofs/hol_light/aarch64/proofs/rej_uniform_eta4_aarch64_asm.ml` | Reference aarch64 proof — canonical structure for what we're aiming the x86 proof to look like. |

## eta4 proof — current state

**The proof file loads end-to-end** against the current (clean) asm.
`MLDSA_REJ_UNIFORM_ETA4_CORRECT` is reduced to three subgoals via
`ENSURES_WHILE_UP2_TAC` (preamble / loop body / post-loop tail).

| Subgoal | PC range | Status |
| --- | --- | --- |
| 1 — preamble (12 instructions: 2nd `endbr64`, 3× broadcast-constant setup, `xorl` of counters) | `pc → pc+56` | **Fully proved** |
| 2 — loop body, one outer iteration (4 sub-iters of the SIMD compaction) | `pc+56 → pc+56` or `pc+318` | **Admitted** (`MLDSA_REJ_UNIFORM_ETA4_BODY_CHEAT`) |
| 3 — post-loop scalar tail | `pc+318 → pc+406` | **Admitted** (`MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_CHEAT`) |

`LENGTH mldsa_rej_uniform_eta4_tmc = 407` (411-byte `.o text` minus
the gcc-auto-inserted leading `endbr64` stripped by `define_trimmed`).

`MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_CORRECT` and `..._MEMSAFE` are
also admitted (CHEAT_TAC) pending the body/tail closures. The
IBT-wrapped `..._SUBROUTINE_CORRECT` / `_MEMSAFE` are commented out
until the underlying NOIBT proofs land.

### What's actually been built around the cheats

The supporting machinery is in place — the cheats are not "we haven't
started", they are "we have the infrastructure but haven't composed it
into a closed proof":

- **Bytecode block (`define_assert_from_elf`)** — freshly regenerated
  from the new clean asm. Bytecode includes the duplicate `ENDBR64`
  inserted by gcc cf-protection plus our explicit one, threshold `248`
  (`MLDSA_N − 8`), buflen guards `256`/`272`
  (`MLD_AVX2_REJ_UNIFORM_ETA4_BUFLEN = 272 = 2 * 136` — note this is
  *not* 136 like the upstream comment used to claim), and mid-iter `ja`
  exits after sub-iters 1, 2, 3.
- **Functional spec** — `REJ_NIBBLES_ETA4`, `REJ_SAMPLE_ETA4_BYTES`,
  and the `LENGTH_REJ_NIBBLES_ETA4` bound lemma (`length ≤ 2 * length input`).
- **Bridge lemmas** — `VAL_WORD_POPCOUNT_LOW8_LE_8`,
  `RAX_BOUND_AFTER_POPCNT_ADD`, `RAX_BOUND_GENERIC`,
  `RAX_AFTER_SUB_ITER`, `RAX_BOUND_AFTER_POPCNT_ADD_DIRECT`. These
  collectively let us reason about `RAX` after a `POPCNTL r10d` of the
  low byte of the mask register.
- **`REABBREV_TAC` capture pattern** — used to pin down the mask
  register and its low-byte image across simulator state-folding
  (s2n-bignum's `X86_STEPS_TAC` aggressively rewrites symbolic state,
  so we abbreviate first).
- **Sub-iter 1** (instructions ~28–37 of the body) — fully stepped at
  the simulator level and the popcount-to-`LENGTH (FILTER ...)` bridge
  is closed.
- **Sub-iter 2** (instructions 34–44) — stepped.
- **Subgoal 3 Case A** — the `jae`-fires path that goes directly to
  `RIP = pc + 443` is established.

### What's left to close `BODY_CHEAT`

1. Finish the symbolic stepping for sub-iters 3 and 4 (mirroring
   sub-iters 1 and 2; the `vextracti128 $1` / `vpsrldq $8` chain into
   `xmm5`).
2. Prove the per-sub-iter `vpshufb`-produces-correct-compacted-output
   lemma (one statement, instantiated four times).
3. Prove `vpmovsxbd` extends each compacted 8-byte block to 8 int32s
   correctly.
4. Show the per-sub-iter increment of `outlen = LENGTH outlist` matches
   `LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST(0, 16*(i+1)) inlist))`.
5. Compose the four sub-iters into a single
   `REJ_SAMPLE_ETA4_BYTES (SUB_LIST(0, 16*(i+1))) =
    REJ_SAMPLE_ETA4_BYTES (SUB_LIST(0, 16*i)) ++ <this iter's contribution>`
   step.
6. Step the `cmp`/`ja` and the trailing `jmp` back to the loop head
   (or out to `pc+318` on the early-exit path).

### What's left to close `SCALAR_TAIL_CHEAT`

- **Case A** (we entered the tail because the SIMD loop's `ja $248`
  fired with `RAX > 248`) — already established that we hit the
  `pc + 406` (function-end) `ret`; need the output-list shape lemma
  showing that the `outlist = SUB_LIST(0, 256) (REJ_SAMPLE_ETA4_BYTES inlist)`
  truncation matches what's in memory.
- **Case B** (we reached the tail with `RCX > 256`) — still needs the
  inner scalar nibble-by-nibble loop stepping plus a
  `REJ_SAMPLE_ETA4_BYTES`-extension lemma for the suffix bytes.

### Annotations now in sync with the new asm

After the asm rewrite, the proof file has been updated end-to-end:
- bytecode block regenerated from the new `.o` (411 bytes raw, 407
  trimmed)
- preamble step range bumped from `(1--11)` to `(1--12)` to cover
  the second `endbr64` plus the broadcast-constant setup
- WOP existence witness changed from `i = 8` to `i = 17` (smallest
  `i` with `16*i > 256`)
- buflen `136 → 272` everywhere (`MLD_AVX2_REJ_UNIFORM_ETA4_BUFLEN
  = 272 = 2 * 136`)
- thresholds: `<= 120 → <= 256` for the `pos` invariant and `<= 224
  → <= 248` for the `outlen` invariant
- PC offsets: `pc + 52 → pc + 56` (loop head), `pc + 286 → pc + 318`
  (scalar tail entry), `pc + 399 → pc + 406` (function exit)
- code length: `LENGTH mldsa_rej_uniform_eta4_tmc = 407`,
  nonoverlapping image `(pc, 407)` (was `(pc, 375)` / `(pc, 400)`)
- outlen-bound lemmas regenerated: `+8` slack carried through, e.g.
  `outlen + val pcnt <= 256` (was `<= 232` for old `outlen <= 224`)
- `SCALAR_TAIL_N_EQ_8 → SCALAR_TAIL_N_EQ_17` (loop now goes up to
  16 outer iterations of 16-byte stride before scalar-tail entry)
- `LENGTH_OUTLIST0_LE_280` rebound to `<= 280` (`248 + 32`)
- `NIBLEN_BOUND_FROM_WOP` rebound to `<= 280`
- a few `_136 / _224` lemmas renamed to their `_272 / _248`
  counterparts

## eta2 proof — current state

`MLDSA_REJ_UNIFORM_ETA2_CORRECT` and `..._MEMSAFE` are full-body
`CHEAT_TAC`. The plan is to do eta4 first, then port the closed
structure over: eta2 has the same outer shape but additionally needs:
- new s2n-bignum instruction models for `vpinsrw`, `vpbroadcastw`,
  `vpmulhrsw`, `vpmullw`, `vpaddd`, `vpsubd` (these are the modulo-5
  reduction path);
- per-sub-iter mod-5 reduction lemma producing `t ∈ {0,1,2,3,4}`.

## Building / testing

The asm is built normally by `make`, but **`AUTO=1`** must be set
(or `OPT=1 AUTO=1`) — without it the build flags do not include
`-mavx2` and the `.S` files compile to empty objects which silently
fall through to the C scalar fallback. KATs still pass either way,
but the asm is not exercised.

```
make AUTO=1 OPT=1 mldsa65
./test/build/mldsa65/bin/test_mldsa65   # KATs
./test/build/mldsa65/bin/bench_components_mldsa65
```

`test/bench/bench_components_mldsa.c` was extended with a
`poly_uniform_eta_4x` benchmark — that's the one that exercises both
`rej_uniform_eta4_avx2_asm` and `rej_uniform_eta2_avx2_asm`.

## Performance notes

`poly_uniform_eta_4x` (median of 20×300 iterations on the test box):

| variant | cycles |
| --- | --- |
| C intrinsics (`-O3`) | ~8400 |
| `dev/x86_64/variants/rej_uniform_eta4_avx2_asm_clean.S` (in production) | ~8700 |
| `dev/x86_64/variants/rej_uniform_eta4_avx2_asm_gcc_derived.S` | ~8520 |

The clean variant is what's being formally verified; it sits ~3.5%
above the intrinsics baseline and ~2% above the gcc-derived variant.
That tradeoff (cleaner code → easier proof) is the one we settled on.

## Why this is a draft PR and not "real" work

- Two `CHEAT_TAC`s remain inside the proof of
  `MLDSA_REJ_UNIFORM_ETA4_CORRECT` (`BODY_CHEAT` and
  `SCALAR_TAIL_CHEAT`), plus the eta2 proof is essentially a stub.
- `MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_{CORRECT,MEMSAFE}` are
  also currently `CHEAT_TAC`-bodied wrappers; the IBT-wrapped
  versions are commented out until those land.
- The bench addition and the `meta.h`/autogen tweaks are scaffolding
  for the perf comparison work and may not survive review unchanged.

This branch is a snapshot of where multi-month work sits today, not a
proposal to merge.
