# ML-DSA Eta4/Eta2 Rejection Sampling Proofs

## Status: Proof Skeletons Complete (Multi-Month Development Ahead)

### Completed Work

1. **Assembly Implementation** (✅ Complete)
   - `rej_uniform_eta4_avx2_asm.S` - 404 bytes of optimized AVX2 code
   - `rej_uniform_eta2_avx2_asm.S` - 549 bytes of optimized AVX2 code
   - Both use SIMD instructions: VPMOVZXBW, VPSUBB, VPMOVMSKB, VPSHUFB, VPMOVSXBD
   - Eta2 additionally uses VPMULHRSW for modulo-5 reduction

2. **s2n-bignum Infrastructure** (✅ Complete - PR #409)
   - Added 4 new AVX2 instruction models to x86.ml
   - Added decode patterns for all 4 instructions
   - Added 40+ simulator test cases
   - Fixed 3 type/decode bugs during development
   - CI validation in progress

3. **Bytecode Extraction** (✅ Complete)
   - Eta4: 404 bytes extracted and filled into proof file
   - Eta2: 549 bytes extracted and filled into proof file
   - Ready for formal verification

4. **Proof Scaffolding** (✅ Complete)
   - Functional specifications defined
   - Main CORRECT theorems structured
   - Memory safety (MEMSAFE) theorems structured
   - Subroutine wrappers for ABI compliance

### Proof Development Roadmap

#### Eta4 CORRECT Proof (Estimated: 4-6 weeks)

**Phase 1: SIMD Loop Correctness** (2-3 weeks)
- [ ] Prove VPMOVZXBW + VPSLLW + VPOR extracts nibbles correctly
- [ ] Prove VPAND masks to 4 bits
- [ ] Prove VPSUBB (nibble - 9) for bound checking
- [ ] Prove VPSUBB (4 - nibble) for eta computation
- [ ] Prove VPMOVMSKB extracts sign bits correctly
- [ ] Prove VPSHUFB table lookup compacts valid nibbles
- [ ] Prove VPMOVSXBD sign-extends to int32 correctly

**Phase 2: Loop Invariant** (1-2 weeks)
- [ ] Define loop state invariant
- [ ] Prove invariant preservation
- [ ] Prove loop termination
- [ ] Prove counter management correctness

**Phase 3: Scalar Fallback** (1 week)
- [ ] Prove scalar nibble extraction
- [ ] Prove scalar bound check
- [ ] Prove scalar eta computation

**Phase 4: Composition** (1 week)
- [ ] Connect SIMD and scalar paths
- [ ] Prove full functional correctness
- [ ] Verify output bounds

#### Eta4 MEMSAFE Proof (Estimated: 2-4 weeks)

- [ ] Prove all memory accesses within bounds
- [ ] Prove no buffer overflows
- [ ] Prove flag states on return
- [ ] Verify nonoverlapping constraints

#### Eta2 CORRECT Proof (Estimated: 4-6 weeks)

All eta4 steps PLUS:
- [ ] Prove VPMULHRSW multiply-high-round-scale with constant -6560
- [ ] Prove VPMULLW multiply low with 5
- [ ] Prove VPADDD combines for modulo-5 reduction
- [ ] Verify reduction produces correct t ∈ {0,1,2,3,4}
- [ ] Prove scalar modulo-5 reduction (imull/shrl/imull/subl)

#### Eta2 MEMSAFE Proof (Estimated: 2-4 weeks)

Same as eta4 MEMSAFE

### Reference Implementation

The proof strategy follows PR #1014 (rej_uniform):
- `/home/ubuntu/mldsa-native-pr1014/proofs/hol_light/x86_64/proofs/rej_uniform_avx2_asm.ml`
- 7200 lines of fully developed proof
- Use as reference for tactics and lemma structure

### Key Proof Techniques

1. **SIMD Reasoning**: Use `EXPAND_SIMD_RULE` for vector operations
2. **Bitwise Operations**: Lemmas for AND, USHR, sign bits
3. **Table Lookups**: Correctness of vpshufb compaction
4. **Modular Arithmetic**: For eta2 modulo-5 reduction
5. **Loop Invariants**: State machine for iteration
6. **Memory Safety**: Bounds checking and nonoverlapping regions

### Testing Strategy

1. Unit test each lemma in isolation
2. Test loop invariant on concrete examples
3. Verify against KAT vectors
4. Cross-check with CBMC contracts

### Timeline Estimate

- **Total Effort**: 12-20 weeks for all 4 proofs
- **Critical Path**: Eta4 CORRECT → Eta2 CORRECT (can parallelize MEMSAFE)
- **Resource**: 1 verification engineer, full-time

### Files

- `rej_uniform_eta4_avx2_asm.ml` - Eta4 proof (currently skeleton with ADMIT_TAC)
- `rej_uniform_eta2_avx2_asm.ml` - Eta2 proof (currently skeleton with ADMIT_TAC)
- `mldsa_rej_uniform_table.ml` - Shared lookup table definition

### Next Steps

1. Wait for s2n-bignum PR #409 to merge (validates instruction models)
2. Begin eta4 CORRECT proof Phase 1
3. Develop key SIMD lemmas
4. Build up loop invariant incrementally
