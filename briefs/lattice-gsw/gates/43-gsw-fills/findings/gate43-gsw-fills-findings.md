# Gate 43: GSW fills — external Codex audit

**Proof-audit verdict: CLEAR for both pinned heads.** There are **0 blockers and 0 majors**. All 35 proofs establish their frozen statements on the accepted routes. **#338 still awaits Seyoon’s GS-01 ruling on disclosed duplication debt and promotion P-1.**

| PR | Audited Lean head | Targets | Blockers | Majors | Minors | Notes |
|---|---|---:|---:|---:|---:|---:|
| [#339 — gsw-core](https://github.com/Shilun-Allan-Li/tcslib/pull/339) | `839f36cca9b4af0570c014f03f19858d0a03cbfb` | 29 | 0 | 0 | 0 | 6 |
| [#338 — gsw-security](https://github.com/Shilun-Allan-Li/tcslib/pull/338) | `d45d3682089cb6fd04f4d075f48a464fefaa143c` | 6 | 0 | 0 | 2 | 4 |

Records: `4ed91289d6132f71ace06b3d9fd87539956d6a88`. Exchange: `14e681e6cfe2e70fb5248fbf2938a024290b061d`. Counts include the confirmed reviewer errata and notes below; there are no additional findings. GS-03’s missing bytes are recoverable and verified.

The audit applies the policy, pack, issued briefs, rulings and Gate 41 dispositions to the reports, changed proofs and relevant providers. Validation comprised independent comparisons against pinned git objects, source review, duplication searches and re-parsing the supplied raw evidence. **I did not repeat native Lean execution.**

The reviewer findings receive these grades. Paths below are relative to `TCSlib/Cryptography/` unless another location is specified.

| Finding | Grade | PR · location | Assessment and disposition |
|---|---|---|---|
| GC-01 | Note; disclosed debt | #339 · `GSW/Eval.lean:262–264` | The getD-of-`List.ofFn` calculation belongs to DL-47. It uses the prescribed public Mathlib lemmas; the report discloses the route and this pin adds the site to DL-47. No undisclosed-copy finding. |
| GC-02 | Note | #339 · `Noise`, `Eval`, `Scheme` | The Boolean integer identities are correct and disclosed. There are eight case-split sites, including three in `homGate_encrypts`. I found no existing public lemma with the asserted integer identities. No major. |
| GC-03 | Note | #339 · `GSW/Symmetric.lean:110–140` | The hand-built equivalence is construction glue using the published augmentation bijection. A composition of `arrowCongr`, `curry` and `piComm` could express the reindexing; the report overstates their inadequacy. No existing public GSW batch-equivalence result is silently re-proved. |
| GC-04 | Note | #339 · sketches at `Scheme:263`, `Symmetric:147` | Both sketches explain the mathematics accurately. Naming private glue is an editorial issue; it does not introduce an API obligation or invalidate the sketches. |
| GC-05 | Note; Rule 10 passes | #339 · `Eval:198–233`; matcher probes | Constructor reduction follows the published statements of `homGate_eq` and `DAGGate.eval_eq`. The sealed direct read fails; the reader route passes. Matcher iota is a limitation of the instrumentation, with no forbidden definition read here. Filing the tooling note remains the stated maintainer disposition. |
| GC-06 | Note | #339 · delivery evidence/reports | Confirmed redundant width rows and citation/count nits. A’s reported file hashes match; B’s final copies match; the lead’s source copies match the audited head. The 45/47 sub-agent evidence files provide adequate provenance despite A’s absent `final/` directory. |
| GS-01 | Note; **ruling pending** | #338 · `Columns:95–192`, `Security:197–238,256–279` | The shared-matrix planting proof and Regev-style relabelling/triangle patterns are disclosed. Retain the proposed debt decision and P-1 payback for Seyoon. The existing positive-length, common-seed shared-parameter hybrid is a relative; no public lemma directly supplies the full differing-seed, shared-parameter interface including zero columns. |
| GS-02 | **Minor** | #338 · REPORT overlap table and P-1 | Confirm the omitted `pair*` and `distAdv_multi_le_sum` relatives and the inaccurate description of the missing abstraction. Differing seed types already exist in `pairHybrid`; the required extension is the shared parameter. Keep the recorded erratum and corrected P-1. **The `distAdv_comp` item is not an undisclosed re-proof**, for the separate reason below. |
| GS-03 | **Minor; reconstructed** | #338 · `evidence/probes/CacheProbe.lean`, REPORT/manifests | The delivery contains 778/779 top-level entries and 771/772 evidence entries. The missing one-line cache probe reconstructs to the exact manifested SHA-256 `f8388ee61e1b1b5ba7d6786f99b895008e3278cb1f06a0063fe1434571d444a1`. Correct the delivery-exactness claim; the supplied reconstruction resolves the evidentiary gap. No proof depends on this probe. |
| GS-04 | Note | #338 · delivered `.pyc` | Manifested, harmless generated material; omit it from future deliveries. |
| GS-05 | Note | #338 · delivered Security “base” seals | The label is imprecise: final Columns enlarged the closure by seven constants. The recorded probes pass; no inference about a repaired read depends on this comparison. This does not invalidate the final seals. |
| GS-06 | Note | #338 · `Security:202–207`; #339 relative at `Symmetric:116,136` | The augmentation-equivalence and translation constructions are disclosed. They cite the bijection rather than re-proving it. A shared `Regev.augmentedEquiv` remains a suitable DW-4 follow-up. |

**GS-02(c), considered independently.** `distAdv_comp` moves deterministic post-processing across an **advantage**, an absolute difference of two acceptance probabilities. The two disputed `have`s at `Security:225–232` establish individual **acceptance-probability equalities**, using the seed bijections `keySeeds` and `unpack`. They apply `acceptProb_comp_equiv`; `acceptProb_def` only identifies the post-processed event with the locally defined test. `distAdv_comp` supplies neither seed equivalence nor these separate probability equalities. An advantage-level rearrangement could use it after other work, but these steps do not silently re-prove it. Its availability in the authorized import therefore does not warrant a major. The minor disclosure erratum for the other relatives remains.

Every target was reviewed; the coverage is:

| PR · unit | Frozen targets accepted | Proof route checked |
|---|---|---|
| #339 · F1 Gadget (5) | `digits_decomposeVec`; `gadget_mulVec_decomposeVec`; `gadget_mul_decompose`; `decomposeVec_block_eq_false`; `errorSum_decomposeVec_le` | Published block/digit identities give both gadget inverses. A zero positional sum has zero terms. Reindexing by `finProdFinEquiv` leaves only the designated block, and the public binary-error-sum bound gives `ℓ·β`. |
| #339 · F2 Noise (12) | `encrypts_gadget`; `encrypts_zero`; `Encrypts.mono`; `.add`; `.neg`; `.sub`; `.sum`; `.mul`; `.mul_bit`; `.mul_le`; `.nand`; `encrypts_chain` | Zero/reused/additive/negated witnesses give the basic closures; subtraction cites addition and negation; finite sums use induction. Multiplication uses the exact witness and asymmetric bound detailed below. The bit corollaries and right-associative chain have the stated noise budgets. |
| #339 · F3 Scheme (6) | `vecMul_secretVector_augmented`; `encrypts_encrypt`; `encrypts_keygen_encrypt`; `decrypt_of_encrypts`; `decrypt_of_encrypts_dyadic`; `decrypt_keygen_encrypt` | Splitting off the last coordinate cancels the secret inner product. Fresh error is a binary subset sum bounded by `m·B`, for every seed. The residual, decoder premise and dyadic indicator are checked below. Basic correctness composes these results. |
| #339 · F7 Symmetric (2) | `encrypts_symEncrypt`; `distAdv_symEncrypt_le` | Reindexed row errors retain bound `B`. Augmentation, column reindexing and translation form a genuine batch equivalence; both inverse laws are proved. Relabelling uniform challenges and inserting a uniform batch gives exactly two DLWE advantages. |
| #339 · F4 Eval (4) | `homAnd_encrypts`; `homGate_encrypts`; `eval_encrypts`; `decrypt_keygen_eval` | Empty, singleton and longer conjunctions satisfy the natural-subtraction formula. Gate cases match the published readers. `runWith_rel` proves the vertex-indexed invariant; the output and leveled condition are read at precisely the stated depth. |
| #338 · F5 Columns (2) | `hashColumns_eq_mul`; `distAdv_hashColumns_uniform_le` | The matrix identity is entrywise. Both planting identities, both seed bijections, update at `⟨k,hk⟩`, both endpoint hybrids and the telescoping bound are correct. The strong single-column LHL receives the shared matrix and independent product coins. |
| #338 · F6 Security (4) | `real_uniformKey_advantage`; `uniformKey_uniform_advantage_le`; `distAdv_encrypt_le`; `distAdv_encrypt_le_of_width` | `acceptProb_bind` gives the exact DLWE equality. The augmentation equivalence preserves the whole key; translation and seed relabelling reduce the statistical gap to F5. The four transitions give two DLWE terms plus `2Nε`; the width corollary multiplies the published scalar bound by nonnegative `N`. |

The critical calculations and boundary cases check as follows.

1. **#339 — multiplication and chain.** With `X` the integer `{0,1}` lift of `G⁻¹(C₂)`, the witness is
   \[
   e(j)=\sum_i e_1(i)X_{ij}+x_1e_2(j),\qquad
   |e(j)|\le N\beta_1+|x_1|\beta_2.
   \]
   The invariant follows from `GX=C₂` modulo `q` and matrix distributivity. The proof retains `x₁.natAbs`; signed integer messages are covered. Every phase-5 use of `mul_bit` has a bit on the left, so the weakening is legitimate. Chain induction follows `Forall₂`, puts the head on the left, and uses
   \[
   N\beta+(\beta_0+kN\beta)=\beta_0+(k+1)N\beta.
   \]
   The empty chain is the accumulator with message `1·x`; Boolean conjunction gives the stated product message.

2. **#339 — decryption.** The private residual lemma proves exactly
   \[
   \operatorname{decrypt}(C)=\operatorname{decode}\!\left(
     \operatorname{codepoint}(b)+\sum_i e_i(G^{-1}w)_i\right),
   \quad w=\lfloor q/2\rfloor e_{n+1}.
   \]
   The sum is an integer sum, then cast modulo `q`. The support lemma and F1 bound its magnitude by `ℓβ`. The decoder is applied with **exactly** `B := ℓβ` and `2ℓβ < ⌊q/2⌋`. This works for odd moduli and signed errors. For `q=2,3`, `⌊q/2⌋=1`, so the premise forces `ℓβ=0`; the residual is the codepoint and decoding is correct. In the dyadic proof, `ℓ≥1` gives `⌊2^ℓ/2⌋=2^{ℓ−1}<q`; digit injectivity proves the indicator at `(last,ℓ−1)`. The sum is one error entry, giving bound `β`, including `ℓ=1`.

3. **#339 — gates and depth.** For list length zero the actual noise is zero, weakened to the stated `β`; length one uses the original ciphertext; longer lists satisfy the displayed recurrence. The `∧`, `∨`, `¬` cases cover arities zero, one and two, with repeated arguments. De Morgan complements add zero noise. In `eval_encrypts`, inputs have depth zero and every argument has depth at most the gate’s depth minus one. Thus one gate changes `(N+1)^{d−1}β` to `(N+1)^dβ`. Acyclicity comes from `args_lt`, and the output is in range by `output_lt`; `IsFaninTwo` is not required. `decrypt_keygen_eval` uses precisely
   \[
   2\ell\bigl((N+1)^L(mB)\bigr)<\lfloor q/2\rfloor,
   \]
   for every key seed and encryption coin matrix, with no extra factor or `L+1`.

4. **#339 — symmetric batch.** The reindexing inverse reads the block and column specified by `rowEquiv.symm`; `apply_symm_apply` and `symm_apply_apply` establish both inverse laws. Translation by the message gadgets is bijective. The real experiment keeps one common secret and all `kN` row errors. At `k=0`, the row and batch spaces are singleton spaces and the same equivalence proof applies.

5. **#338 — columns and security.** In `H_k`, columns below `k` are uniform; the rest are hashes under the same matrix. Planting a real column gives `H_k`; planting a uniform column gives `H_{k+1}`. The auxiliary coins have type `Cols × ρ`, finite and nonempty, and are independent of the challenge. The test receives the matrix, so the **strong** LHL applies. At `N=0` the hybrid sum is empty. There is no whole-matrix universality claim. The Security sampler identity retains the public key, uses `hashColumns_eq_mul`, and translates by `μG`. The chain is real `μ₀` → uniform-key `μ₀` → uniform → uniform-key `μ₁` → real `μ₁`, giving two exact DLWE terms and two `Nε` terms. Finally `2(Nε)=N(2ε)≤N·2^{−κ}` under the frozen width assumptions.

**Frozen surface, reuse, Rule 10 and sources.** Independent normalization of each complete file, removing only authorized proof/sketch changes and additions, gives equality. All 35 headers and statement prose are byte-identical; header/prose mutation controls fail and sketch-only controls pass. The only additions are #339’s three private helpers and #338’s two authorized imports. All 50 supplied import-closure files byte-match their pinned git objects, and both supplied diffs match git’s diffs with the recorded hash abbreviation.

The reuse search covered the binary subset-sum, decryption-residual, gadget, circuit-host, symmetric-Regev and hybrid families named in the pack. I found no additional undisclosed public or private duplicate. The proofs cite `LWE.binaryErrorSum_bound`, the gadget readers, `runWith_rel`, the probability lemmas and the scalar extraction bound rather than re-proving them. The remaining disclosed patterns have the dispositions above.

Rule 10 passes by source inspection and the checked seal evidence. The `change`/`rfl` steps reduce permitted Mathlib constructions; the residual’s `dsimp only` follows `Regev.decrypt_eq` and reduces projections. `Regev.augmented` is used as a function with its published bijectivity theorem, without a body read. No forbidden definition selector was found. GC-05’s published-reader reduction is acceptable independently of the seal’s matcher limitation.

All target sketches describe their delivered proofs; the three private helpers have appropriate glue docstrings. Citation groups are unchanged. Checking the cited passages against the DW-7 GSW13, AP14, BV14 and extended Pei16 transcriptions found no fabricated or misplaced target citation. The documented transpose, deterministic decomposition, worst-case noise and decryption-column deviations remain explicit. `[Vad12]`’s absent registry entry is a pre-existing source-registration note.

**Evidence verification.** The pack manifest verifies 11/11 files; `verification.zip` verifies 137/137 entries with an exact path set. The review ZIPs verify 1095/1095 and 1022/1022 inner entries. Worker manifests verify 544/544 and 533/533 for core; security has only the reconstructed GS-03 omission described above.

I re-parsed both 650-module build records and checked every module log’s recorded digest: return codes are zero, with zero Lean errors in either form, and owned source hashes match the pinned heads. All 20 core and eight security seals have matching install/EOF counts and zero errors. Removing their recorded harness insertions reconstructs the audited source bytes exactly. Declaration-range checks of 40 core and 16 security control runs account for all 180 and 64 expected failures, respectively, including the strict coercion artifact. The axiom and dependency records show only `propext`, `Classical.choice`, `Quot.sound`, with no sorried dependency reached by a target. #338 reaches only core’s `encrypt_eq` and `lift_apply` readers, not its filled targets.

The empty records copy of core’s evidence manifest, the unfiled tooling note and the unapproved GS-01 ledger row retain the pack’s stated maintainer dispositions. The combined build on the tip `201bf57a` remains the maintainer’s merge condition, outside this audit. Either merge order is compatible with the disjoint changes.

Notation: `n`, `m`, `q` are LWE dimension, sample count and modulus; `ℓ = P.width`; `N = P.columns = (n+1)ℓ`; `ε = Regev.extractionError P.lwe`. The `β` parameters and `B` are the indicated noise bounds, and `L` is the allowed circuit depth. The `e` vectors are integer error witnesses; `X` is the integer binary lift of `G⁻¹(C₂)`; `w` is the half-modulus target vector, using the last standard basis vector `e_{n+1}`; `H_k` is the column hybrid with its first `k` columns uniform. Other symbols are the corresponding theorem parameters.
