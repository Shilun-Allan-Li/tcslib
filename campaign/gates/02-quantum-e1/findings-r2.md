# TCSlib quantum epoch E1 round 2 audit findings

**Result: 0 blockers, 0 majors, 3 minors, 1 note.** Both round-1 debt majors are repaired. The cumulative statement freeze holds. The remaining findings concern policy compliance and documentation; none identifies an incorrect new public statement or a remaining wholesale copy in the E1 files.

**Scope.** The five `TCSlib/Quantum/Basic/` files at `647511e33e2c8b2a8c567362b0f3c756da78d2c9`, compared with the gate baseline `13c8664b44f2550a66a8fb2c94c73069614f072f` and round 1 at `a97fceca7c0f7b360f91cb08d4db5a5b33bdb548`. Line numbers below refer to the repaired Lean sources or the named section extracted from the supplied bundle. Proof bodies were inspected for their mathematical routes, reuse, and documentation, not for tactic correctness. Lean elaboration and kernel/axiom provenance remain supported by the supplied execution evidence; this audit did not recompile the project.

## Findings table

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | minor | `Register.lean:183`; `Gates.lean:105`; `ApplyOn.lean:157,186,257,260,366`; `Measure.lean:131`; `Protocols.lean:92,96,189,407` | The specifically reported TCSlib cross-file unfoldings were repaired, but E1 still explicitly unfolds core/Mathlib definitions contrary to the attached policy §1. | Examples are `simp only [mulVec, dotProduct]`, `simp only [Function.comp, …]`, and `simp […, finTwoArrowEquiv]`. At the pinned Mathlib revision, `dotProduct`, `Matrix.mulVec`, and `finTwoArrowEquiv` are definitions, not equation lemmas. The policy expressly forbids passing core/Mathlib definitions to `simp`, `rw`, or `unfold`; it permits definitional reduction in `rfl`, `decide`, or `show`. These uses belong to E1 additions or former `sorry` bodies. | Replace the explicit definition unfoldings with appropriate interface lemmas or a permitted definitional `show` step. This is an abstraction-policy issue, not a claim that the proofs are incorrect. |
| R2-2 | minor | `campaign/fills/e1/REPORT.md:101–113,139–156` · historical duplication ledger and errata | The corrected report still asserts the historical absence of duplication after round 1 established two counterexamples. | Its ledger says all 21 E1 rows are idioms and “Copies of proved material: none.” The errata acknowledge the duplicate `example`, but do not explicitly supersede that assertion or correct the Hadamard classification. The historical count 21 is valid for `a97fceca`; the classification is not. The current 15-row ledger in `resolutions.md` is correct. | Mark the historical classification as superseded, identify both admitted duplicates, and point to the repaired ledger. Keep historical counts tied to their commit. Under workflow §4, this is a correction to an already acknowledged debt family, hence minor. |
| R2-3 | minor | `resolutions.md:16`; `REPORT.md:120–127` · counts | Two small accounting statements remain inaccurate. | Across the five Basic files, gate → round 1 is **134 → 168 named declarations**, plus one unchanged anonymous instance; 135 → 169 includes that instance and must not be labelled “named.” Separately, the list introduced as “Sixteen sketches” contains **17** declarations. The current ten-file figures 211 → 248 and 245 → 248 are correct. | Correct the resolutions' description and the report's sketch count. Preserve the prior auditor's verbatim `findings.md`; record its inherited count correction in the resolutions. |
| R2-4 | note | `Protocols.lean:353` · `pow_mul_self_of_mul_self` | The new short power helper can directly reuse a pinned Mathlib lemma; it does not need promotion to a new public TCSlib theorem. | [`pow_mul_pow_eq_one`](https://github.com/leanprover-community/mathlib4/blob/029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e/Mathlib/Algebra/Group/Basic.lean#L170) proves, in any monoid, `a * b = 1 → a ^ m * b ^ m = 1`. Taking `a = b = g` gives the helper exactly. The current implementation is one elementary rewrite chain, not wholesale copied proof material. | No change required for this audit. Optional simplification: keep the private interface and use `pow_mul_pow_eq_one m h`, or invoke that lemma at the two consumers. |

## 1. Repair by repair verification

| Round-1 finding | Verification and disposition |
|---|---|
| 1 — duplicate measurement example | **Repaired.** The repair diff deletes precisely the anonymous restatement and its two-line proof. `Ket.probQubit_basis` remains at `Measure.lean:111`. There is no `example` command in the five repaired files or the two additional copy-screen files. The owner's acknowledgment is recorded in the supplied resolutions. |
| 2 — duplicated Hadamard-square calculation | **Repaired using the proposed construction.** `hadamardMat_conjTranspose` and `hadamardMat_mul_self` precede `hadamardMat_mem_unitaryGroup` and `Gate.H`. The square calculation occurs once, in `hadamardMat_mul_self`. Unitarity rewrites the adjoint product using both lemmas; `Gate.H_mul_H` is `Subtype.ext hadamardMat_mul_self`. `gate1_ext` delegates its entry comparison to `mat1_ext`. The owner's acknowledgment is recorded. |
| 3 — inaccurate sketches | **Repaired.** `applyOn_permMat_mulVec_apply` now names `Finset.sum_eq_single`, which the code uses. The Hadamard unitarity sketch describes the self-adjointness-plus-square route. The sketches of the square and gate-square lemmas describe their respective computation and delegation. |
| 4 — broader coordinate formulas and input/output wording | **Repaired.** Both coordinate lemmas explicitly accept arbitrary matrices and vectors and identify the unitary textbook setting as a specialization. The one-wire docstring calls `a` the input bit and `y i` the output bit. Neither signature changed. |
| 5 — missing step markers | **Repaired.** `applyOn_mul_applyOn_of_disjoint` marks the candidate register, surviving term, evaluation, and uniqueness. `no_cloning_of_overlap` marks input/output pairings, unitary preservation, and the modulus contradiction. `teleport_outcome_prob` marks reindexing, unitary normalization, bijection obligations, and summand identification. These are comment-only changes. |
| 6 — TCSlib cross-file unfoldings | **Repaired as reported.** The ten explicit uses on nine lines of `flipAt`, `cnotMap`, and `hadamardMat` in `ApplyOn` and `Protocols` now use `flipAt_eq`, `cnotMap_eq`, and `hadamardMat_apply`. R2-1 concerns additional core/Mathlib uses covered by the broader policy, not failure to perform these substitutions. |
| 7 — order and anonymous boundaries | **Repaired for this audit surface.** `drift.py` separates `example` and unnamed `instance`, compares carried-over named order, and inventories anonymous commands. The screen wrapper explicitly checks for examples before invoking the unchanged shared screen. The present no-example result was independently checked. See the tooling limits below. |
| 8 — report and counter descriptions | **The specified corrections are accurate.** At the round-1 commit there are nine ApplyOn private helpers and 28 overall; the 19 inherited theorem dependents comprise 18 source equation lemmas plus `Ket.nonempty_reg_zero`; the anonymous instance is outside the campaign lint's public subtotal; the sweep counts warning/error lines rather than all messages. R2-2 and R2-3 identify other residual report inaccuracies. |
| 9 — axiom changes by kind | **Repaired.** Re-running `axiom_diff.py` on the pinned historical censuses and supplied current census reproduces all three attached breakdowns: gate → round 1, gate → repaired, and round 1 → repaired. The census is correctly described as non-internal constants rather than all declarations. |

The two smaller reuse suggestions were also implemented: `extend_wire` replaces the repeated extend/update argument, and the common power helper replaces `X_pow_mul_self` and `Z_pow_mul_self`. The resolutions explicitly record acceptance of the single-owner fill and in-place promotions. This audit verifies the supplied record; it does not independently authenticate the historical owner decisions.

## 2. Independent cumulative freeze check

Both supplied diffs reverse-apply to the repaired sources. The reconstructed old files and repaired files match every old/new Git blob-hash prefix in the diffs. For the cumulative diff:

| File | Baseline blob | Repaired blob | Named declarations | Former `sorry` bodies replaced | Other baseline named bodies unchanged |
|---|---|---|---:|---:|---:|
| Register | `1831c432` | `a85e6c14` | 29 → 32 | 10 | 19 |
| Gates | `8a8aae74` | `ff76b148` | 48 → 56 | 15 | 33 |
| ApplyOn | `e9962ab7` | `7956c322` | 21 → 34 | 11 | 10 |
| Measure | `405b40f4` | `70de7361` | 11 → 13 | 6 | 5 |
| Protocols | `a9bccc36` | `63522331` | 25 → 36 | 10 | 15 |
| **Total** | | | **134 → 171** | **52** | **82** |

This census separates the unchanged anonymous `Decidable (AgreeOff …)` instance. Including it gives 135 → 172 source declarations; excluding private helpers gives **135 → 143 public source declarations**. The 37 additions are eight public theorems and 29 private helpers. No baseline declaration was removed, renamed, re-signatured, or reordered. Every changed baseline proof body was exactly `by sorry` after comments and whitespace were removed. All baseline definitions and already-proved bodies remain unchanged.

The independent comparison used nested-comment stripping, scope-qualified declaration identities, a bracket-aware signature/body split, and a separate comparison of the surrounding commands. The only surrounding-code change is `open Matrix` in Measure. It supplies matrix notation; it does not alter the existing statements. There are no changed imports, namespaces, variables, options, or attributes hidden outside the compared declarations. The GitHub baseline-to-repaired path comparison also confirms that these are the only changed TCSlib source files.

The supplied ten-file drift script was separately rerun on the reconstructed snapshots, with the five unchanged counting files fetched at the audited revision. It reproduces **211 → 248 named declarations, 159 unchanged, 52 changed bodies, no signature changes or removals**, and unchanged carried-over order. Against round 1 it reproduces **245 → 248, 232 unchanged, 11 changed bodies, five additions, two private removals**.

The eleven round-1-to-round-2 body changes are all allowed:

| Category | Declarations |
|---|---|
| Six former gate-baseline `sorry`s | `hadamardMat_mem_unitaryGroup`, `Gate.H_mul_H`, `applyOn_wire_X_mulVec_basis`, `applyOn_wires20_CNOT_mulVec_basis`, `teleportState_vec`, `teleport_correct` |
| Five E1 additions | `Gate.gate1_ext`, `applyOn_wire_mulVec_apply`, `cnot_extend_wires01`, `flipAt_const`, `superdenseState_vec_aux` |

The deleted `X_pow_mul_self` and `Z_pow_mul_self` were private E1 additions. The deleted anonymous example was absent from the gate baseline. None of these deletions violates the audited freeze.

## 3. New public declarations and private helpers

The following restatements were formed from the signatures and definitions before comparison with the declarations' docstrings.

**`Quantum.hadamardMat_conjTranspose` (`Gates.lean:233`).** The conjugate transpose of the concrete complex matrix `hadamardMat`, indexed by one-qubit registers, is that same matrix. Its entries are real, so conjugation does nothing; swapping its indices preserves the product of the two bits in its exponent. Thus every adjoint entry agrees with the original entry. This matches the docstring and entrywise sketch, without a unitarity assumption or a circular appeal to `Gate.H`.

**`Quantum.hadamardMat_mul_self` (`Gates.lean:242`).** Multiplying that concrete matrix by itself gives the identity matrix on `Reg 1`. Under the identification of the two constant registers with `0,1`, it is `(1/√2) [[1,1],[1,-1]]`; its square is `(1/2) [[2,0],[0,2]]`. The normalization is valid because `√2` is nonzero. This matches the docstring, the four-entry computation in the sketch, and the Hadamard gate of [de Wolf v6, §1.4, printed p. 9](https://homepages.cwi.nl/~rdewolf/qcnotes.pdf#page=21).

Neither statement is vacuous: `Reg 1` has exactly two elements and the entries are fixed complex numbers, with no hypothesis that could be inconsistent. Both declarations are correctly placed before unitarity and the bundled gate, and both appear in `## Main results`.

No hidden duplicate of either concrete Hadamard theorem was found in the pinned Mathlib matrix interfaces. The pin is `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, verified from `lake-manifest.json`. Its `Matrix/Hadamard.lean` concerns the **entrywise product**, not the quantum gate; the `Hermitian` and `ConjTranspose` APIs provide general infrastructure but do not establish these facts about TCSlib's concrete `hadamardMat`. This is a targeted dependency check, not a claim to have semantically compared every Mathlib theorem.

The six earlier public additions have unchanged signatures. Their round-1 restatements in the attached `findings.md`, answer 2, remain applicable. The two amended coordinate docstrings accurately distinguish the arbitrary-matrix formulas from de Wolf's unitary gates (§§1.4 and 2.1.2); the input/output convention is now explicit.

| New private helper | Mathematical content and placement |
|---|---|
| `mat1_ext` (`Gates:211`) | Every function `Fin 1 → Qubit` is constant, so agreement on the four constant row/column pairs implies matrix equality. It factors a finite-index representation detail for two consumers in Gates. No public promotion is required now. |
| `extend_wire` (`ApplyOn:409`) | At the selected wire, extension writes `u 0`; elsewhere both extension and update retain `y`. It is shared by two local consumers and belongs naturally beside `wire`. A public equation could become useful to future clients, but the present patch creates no cross-file copy or mandatory promotion. |
| `pow_mul_self_of_mul_self` (`Protocols:353`) | If `g² = 1`, then `g^m g^m = (g²)^m = 1`, including `m = 0`. The fact is general monoid algebra, already supplied more generally by Mathlib's `pow_mul_pow_eq_one`; see R2-4. Do not introduce another public TCSlib generalization merely to expose this local wrapper. |

## 4. Duplication check and cumulative ledger

The pinned repository `scripts/copy-text-screen-v3.py` was fetched and run on the five repaired files plus the two pinned error-correction files. Its output matches the supplied screen body exactly: **132 screened declarations, 22 directional rows, 2,939 reproduced characters**. These are directional, thresholded text matches, not 22 independent mathematical duplicates and not a copied-material fraction.

All fifteen E1 rows are classified below; arrows denote the screen's “target reproduces source” direction.

| Rows | Exact directions | Classification |
|---:|---|---|
| 10 | `X_mul_X → Z_mul_Z`; `S_mul_S → Z_mul_Z`; `H_mul_Z_mul_H → Z_mul_Z`; `H_mul_Z_mul_H → X_mul_X`; `Z_mul_Z → S_mul_S`; `X_mul_X → S_mul_S`; `H_mul_Z_mul_H → S_mul_S`; `Z_mul_Z → X_mul_X`; `S_mul_S → X_mul_X`; `X_mul_X → H_mul_Z_mul_H` | Shared finite-case/simplification idiom for four different identities. The common matrix/gate extensionality step is factored. |
| 4 | `X_mulVec_apply → cnot_mulVec_apply`; `teleportState_vec_sum → cnot_mulVec_apply`; `cnot_mulVec_apply → X_mulVec_apply`; `teleportState_vec_sum → X_mulVec_apply` | Uses of the shared permutation-action lemma and involution conversion. The specialized permutations and ambient registers differ. The general sum argument is not re-proved. |
| 1 | `superdenseState_vec_aux → teleportState_vec` | Common closing case-split/normalization idiom for two different protocols. The amplitude formulas, inputs, and outputs differ. |

The seven older rows are two directions each for Singleton's left/right scalar identities and left/right additive identities; two directions between Hamming's `KnillLaflamme` and `IsNondegenerate`; and `cleaning_dimension_identity → card_add_compl`. They remain entirely within the unchanged older files. No row crosses between E1 and those files.

The six E1 rows removed since round 1 are the example's misattributed Measure row, the two directions between `H_mul_H` and `hadamardMat_mem_unitaryGroup`, and the three other rows involving `hadamardMat_mem_unitaryGroup`. This reconciles 21 → 15.

The semantic check also examined copies too short or too differently written for the screen:

- `applyOn_mul` obtains the relevant column from `applyOn_mulVec_apply`, so the filtered-sum bijection is established once.
- Protocols' `permMat_mulVec_apply` specializes `applyOn_permMat_mulVec_apply` through `applyOn_refl`; it does not redo the single surviving term argument.
- `inv_sqrt_two_sq` delegates to `inv_sqrt_two_mul_self`; the norm-preservation theorem delegates to `inner_mulVec_of_mem_unitaryGroup`; consumers use the public register-splitting equation.
- `superdense_decode` and `superdenseState_vec` reuse `superdenseState_vec_aux` instead of repeating its computation or moving an audited declaration.
- The one-wire extension argument and the two power arguments have been consolidated. The remaining Mathlib power reuse opportunity is the short one recorded in R2-4.
- `H_mul_Z_mul_H` computes **a different fact** from `H H = 1`: its middle factor contributes an additional `(-1)^z`, changing the character sum from the equality indicator to the bit-flip indicator. Shared Hadamard entries and normalization do not make these two proofs copies of the same theorem.

No remaining wholesale duplication was identified in the repaired E1 surface. The current resolutions ledger is accurate; the historical fill-report classification needs the explicit supersession in R2-2.

## 5. Tooling and evidence

**Drift.** The repaired script addresses the two concrete round-1 omissions: named order and anonymous command boundaries. For the present files, its census agrees with the independent comparison. It is still a source-text heuristic: comment stripping is not nested-comment aware; names are keyed by file and short name rather than full namespace; its signature split uses the first `:=`, not a depth-aware parser. These limitations did not affect the present comparisons. Anonymous commands were additionally compared in full: the ApplyOn instance is unchanged, and only the unaudited example disappears.

**Copy-screen boundary guard.** Listing examples separately is an adequate bounded workaround here because the list is empty and that was independently checked. It is not a general repair to the shared parser. A future nonempty list must invalidate an automatic interpretation of that screen's rows until the examples are separately delimited and inspected.

**Axiom classifications.** The attached `axiom_diff.py` classifies the actual changed names correctly:

| Comparison | Added constants | Removed constants | Carried-over constants changing from `SORRY` to `CLEAN` |
|---|---|---|---:|
| Gate → round 1 | 22 = 6 source theorems + 12 generated equations + 2 matchers + 2 `congr_simp` | 0 | 90 |
| Gate → repaired | 21 = 8 source theorems + 11 generated equations + 2 `congr_simp` | 0 | 90 |
| Round 1 → repaired | 2 source theorems | 3 = `cnotMap.eq_1` + the two one-wire matchers | 0 |

These changes agree with workflow §4's distinction between source declarations and elaborated auxiliary constants. The classifier is not a complete future-proof implementation of every category in that policy: for example, `_simp_N` and publicly generated instances for private types would need additional handling if they occurred. Neither occurs among these additions/removals.

The current supplied census has **267** entries, including **174 Quantum constants**, all tagged clean and depending only on subsets of `propext`, `Classical.choice`, and `Quot.sound`. The **33** remaining `SORRY` entries lie outside Quantum. The 90 cleaned carried-over constants comprise 52 filled theorems, 19 definitions, and 19 other theorems, consistent with the inherited-dependency account. These counts were independently recomputed from the logs; they are not a new Lean axiom-probe execution.

The sweep log reports 14 successful modules and 33 sorry warnings, distributed 3 + 2 + 15 + 8 + 5 across the five Promise/Counting implementation modules. Its seven Quantum rows have zero sorry warnings and zero other warning/error lines. The descriptions now accurately delimit those counters. The five supplied Lean files also independently satisfy the stated 100-character line limit.

## 6. Proof sketches and documentation

Every repaired body was checked against its sketch or short statement docstring:

| Repaired declaration(s) | Route described and implemented |
|---|---|
| `hadamardMat_mem_unitaryGroup`, `Gate.H_mul_H` | Reuse the matrix-level adjoint/square lemmas; no second square calculation. |
| `Gate.gate1_ext` | Lift the four-entry matrix equality with `Subtype.ext`. |
| `applyOn_wire_mulVec_apply` | Reindex `Reg 1` by its bit and use `extend_wire`. |
| `applyOn_wire_X_mulVec_basis` | Use placed-permutation basis action, then identify extension with the appropriate update/flip. |
| `applyOn_wires20_CNOT_mulVec_basis` | Use placed-permutation basis action and identify the three wire coordinates. |
| `cnot_extend_wires01`, `flipAt_const` | Identify the concrete updated register through the public gate equations. |
| `teleportState_vec` | Reduce to the two-term sum, compare eight bit cases, and normalize the Hadamard factors. |
| `teleport_correct` | Express Bob's unnormalized state, cancel the two adjacent equal powers, and apply matrix-vector composition. |
| `superdenseState_vec_aux` | Expand the placed gates through the shared action formulas and compare sixteen input/output cases. Its public counterpart explains this computation and delegates to it. |

The new `hadamardMat_conjTranspose` and `hadamardMat_mul_self` sketches match their entrywise routes. The three new private helpers have accurate short mathematical descriptions. The three comment-only repairs match the proof boundaries they identify. No stale route was found in these changed proofs.

The rest of the cumulative E1 sketches were also checked, including every filled statement. The coverage is:

| File | Filled statements and implemented routes |
|---|---|
| Register — 10 | `card_reg` by finite-function cardinality; both append restrictions by equivalence evaluation; basis/reindex/product normalization by finite sums; unitary norm preservation through the shared inner-product lemma; `evolve_mul`/`evolve_one` by the matrix action; empty-basis impossibility by normalization. |
| Gates — 15 | Permutation unitarity and basis action by indicator sums; diagonal unitarity by entry norms; bit-flip involutivity pointwise; Hadamard unitarity and square by the shared matrix results; phase norms; the X/Z/S and HZH identities by their four entries; `X_ne_one` by an off-diagonal entry; X from H/S by the earlier identities; Toffoli's controlled slice by the finite bit-map comparison. |
| ApplyOn — 11 | Identity via on/off-wire equality; multiplication by the shared vector-action formula on a column; adjoints by symmetry; unitarity from those algebraic identities; full-wire placement by a vacuous off-wire condition; disjoint commutation through the unique intermediate-register helper; Kronecker compatibility by register splitting; basis action by a column; zero-wire placement as a scalar; the X/CNOT placement sanity identities by placed permutation action. |
| Measure — 6 | Nonnegativity and the upper bound by nonnegative finite sums; two-outcome normalization by complementary filters; basis determinism by a single term; off-wire invariance through projection commutation and unitary norm preservation. |
| Protocols — 10 | Pairwise no-cloning by overlap modulus, universal no-cloning by a nonorthogonal pair, exact-vector no-cloning by opposite phases; Bell normalization; initial-state register splitting; teleportation amplitudes and outcome probability; inverse corrections; the two superdense results through the single exact-state helper. |

The module summaries and main-results entries describe the current API. The two coordinate docstrings' source qualifications are accurate. The corrected historical helper/axiom/counter descriptions are accurate for their stated round-1 commit, not proposed current totals. The residual documentation errors are R2-2 and R2-3.

## 7. Answers to the seven questions

1. **Repairs:** the nine targeted repairs are verified; major 2 implements the proposed matrix-level construction. The historical report still needs the explicitly identified corrections.
2. **Freeze:** yes. The cumulative diff changes only the 52 former audited `sorry` bodies and documentation within audited declarations. All eleven subsequent body changes are in those fills or E1 additions.
3. **New declarations:** both are true, nondegenerate, accurately documented, and correctly placed. No matching concrete Hadamard theorem was found in the checked pinned Mathlib interfaces. No new private helper requires public promotion now; the power fact already has a general Mathlib home.
4. **Debt:** the fifteen remaining E1 rows are shared idioms for distinct results. The semantic check found no remaining wholesale copy. HZH is a different character-sum identity from HH. The small power-lemma reuse opportunity is recorded separately.
5. **Tooling:** the concrete anonymous-boundary and order omissions are fixed for these files; the no-example guard is adequate here. The axiom-kind breakdown is correct for the actual names. The tools' general limitations are stated above.
6. **Documentation:** every repaired proof's sketch describes its mathematical route; the cumulative sketches also match. The report's specified round-1 corrections are accurate, but its historical duplication classification and two accounting descriptions need correction.
7. **Anything else:** no new incorrect statement, freeze violation, or substantive mathematical regression was identified. R2-1 records an additional policy inconsistency not caught by the reported zero-finding lint. This is a scoped audit result, not a blanket approval of the project or an independent kernel recheck.

## Evidence identity

The supplied `quantum-e1-r2-bundle.md` is 326,038 bytes, with 30 attachment section headers plus the initial pack. Its SHA-256 is `b7d6d29769401c3c8faa45f4d1b1fe246e9a372d959c49dbfc12458f781458c7`.

External checks used pinned TCSlib sources and Mathlib at the revisions stated above. The de Wolf source was checked at the author's PDF, whose title page identifies arXiv:1907.09415v6, 27 August 2026. No repository source was edited as part of this audit.
