# TCSlib quantum phase 1 round 2 audit findings

At commit `4b2c72b3aea92bbe05cb3c2d1af9d1e51310e896`, I find **0 blockers, 0 majors, and 3 minors**. The two round-1 majors are substantively repaired. I found no counterexample to a new or changed Lean theorem; the remaining findings concern explanatory prose.

I compared the two supplied bundle snapshots, including definition bodies, and checked the supplied evidence. I did **not** rerun Lean or review tactic proofs. The admissions remain admissions.

Round-1 baseline: `d2d72d18ed5b5845ff25ae028490ee45600ae38f`. Repository: `Shilun-Allan-Li/tcslib`, branch `quantum/p1-basic`. This file exports the round-2 report from the audit conversation; citation widgets have been replaced by ordinary links for forwarding.

## Findings table

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `TCSlib/Complexity/Counting/GapP.lean` · module introduction, lines 18–25 | The scaled-amplitude explanation is correct for the intended unitary purification, but describes the gate set of Watrous §III.2 without stating that restriction. | That gate set includes erasure. Preparing a Bell pair and erasing one qubit produces `I/2`, which has no pure-state amplitude vector. The plan’s FD-4 already specifies purification and excludes erasure from the core, so this is a local scope mismatch rather than a defect in the intended construction. Watrous distinguishes these models explicitly. [Watrous, §§III.2–III.3](https://cs.uwaterloo.ca/~watrous/Papers/QuantumComputationalComplexity.pdf). | Begin: “For computational-basis inputs to the unitary purification specified in FD-4, retaining all discarded wires…” Then retain the numerator and denominator explanation. |
| 2 | minor | `TCSlib/Quantum/Basic/ApplyOn.lean` · `applyOn_commute_of_disjoint`, proof sketch, lines 139–145 | The corrected intermediate-register assignments are right, but the sum need not have “a single nonzero term.” | Take `U₁ = 0` and `U₂ = 1`, on disjoint wires. Every summand is zero. When the outside coordinates agree, exactly one intermediate register satisfies the placement constraints, but its matrix-entry product can vanish. | Replace “a single nonzero term” with “at most one nonzero term, at the unique intermediate register satisfying the outside-wire constraints.” No statement change. |
| 3 | minor | `TCSlib/Complexity/Counting/GapP.lean` · `coinFill` docstring, lines 193–197 | The new short-string sentence overstates failure of the probability formula. | Let `M` always return `some true`, take `p \|x\| = 2`, and count seeds of length `m = 1`. Acceptance is `1`, and the displayed expression is also `1/2 + 4/8 = 1`. The formula can hold without the guard; the guard guarantees it uniformly. | Say “On shorter strings, abstentions use the `false` default, and the formula need not hold.” No definition or theorem change. |

These findings do not revive either round-1 major.

## Repair verification against all round-1 findings

| Round-1 finding | Round-2 disposition |
|---|---|
| **1 — exact-vector no-cloning presented as physical no-cloning** | **Repaired.** The two-state and universal theorems now permit output phases. The old phenomenon is separately named and accurately described by `no_exact_cloning`. All three statements are true; arguments appear below. |
| **2 — raw quantum gate entries called GapP functions** | **Repaired in substance.** The paragraph now distinguishes integer numerators from complex amplitudes and states the denominator. Finding 1 above requests the missing purification qualifier. |
| **3 — superdense message-label convention** | **Repaired.** The divergence records the `01`/`10` interchange and the global sign at `11`. The implementation is unchanged, and the new exact-state theorem agrees with it. |
| **4 — incorrect commutation intermediate register** | **Repaired in substance.** Both multiplication orders now have the correct assignments. Finding 2 above concerns only the claim that the surviving contribution is nonzero. |
| **5 — missing coin-fill guard and default** | **Repaired in substance.** Both are now stated. Finding 3 above corrects the overstatement about what happens outside the guard. |
| **6 — `Eff ≡ False` test** | **Repaired by the pack erratum.** Five closure implications are vacuous; `HasConstVerifiers` fails, as do PP and GapP membership witnesses. |
| **7 — incomplete lint coverage and declaration count** | **Repaired.** The new campaign-style log lists all 14 files. The count explicitly includes the anonymous decidability instance. The facade import change is discussed below. |
| **8 — AB09 tie convention** | **Repaired.** The prose distinguishes strict and non-strict thresholds and restricts the equivalence claim to polynomial time. For integer gaps, `f ≥ 0 ↔ f + 1 > 0`, and `f > 0 ↔ f − 1 ≥ 0`. The [authors’ draft](https://theory.cs.princeton.edu/complexity/book.pdf) independently confirms the non-strict convention. |
| **9 — definitions inheriting `sorryAx`** | **Disposition remains appropriate.** Existing definition bodies are unchanged; the census still lists 19 affected definitions. The new `Ket.nonempty_reg_zero` theorem inherits the admission through `Ket.basis`. |
| **10 — missing standard-GapP bridge** | **Acceptable deferral to Q0.10.** No current statement asserts that the bridge has already been formalized. |
| **11 — acknowledged duplication** | **No new acknowledgment required.** The additions remain within the approved ket, elementary-gate, and Born-rule layer. I found no expansion into an additional body of duplicated infrastructure. The namespace screen remains only a collision check. |

## Independent definition restatement

I read comment-stripped declarations and recorded this restatement before reading the new definition’s docstring.

| Definition | Independent mathematical restatement | Subsequent comparison |
|---|---|---|
| `Quantum.wires20` — `ApplyOn.lean:208` | An injection from two local wire positions into three global positions: local wire `0` goes to global wire `2`, and local wire `1` goes to global wire `0`. Global wire `1` is outside its image. The order matters. | The docstring agrees exactly. This is a representation helper, not a separately attributed textbook definition. Together with `applyOn`, it places the first CNOT wire—the control—on global wire `2`, and the target on global wire `0`, consistently with the local-gate interpretation in de Wolf §2.1.2. |

This is the **only new definition**. No existing definition body changed.

For the unchanged surface, I carry forward the supplied round-1 restatements **D01–D63**, the admitted-theorem arguments **S01–S35 and S37–S72**, and its inventory of other theorem statements, after checking declaration-text stability. Round-1 **S36** is superseded by the fresh no-cloning analysis below.

## Every new or changed directly admitted theorem

There are **14** such statements: 13 additions and the changed `no_cloning`.

1. **`Register.lean:96` · `card_reg`.**
   A register label independently assigns one of two values to each of `n` positions, so there are `2^n` labels. At `n = 0`, the unique empty function gives cardinality one, agreeing with `2^0`.

2. **`Register.lean:247` · `Ket.isEmpty_of_isEmpty`.**
   On an empty basis, the sum in a ket’s normalization field is the empty sum, hence zero. A ket would therefore supply `0 = 1`, so no ket exists.

3. **`Gates.lean:276` · `Gate.X_mul_X`.**
   `X` adds one modulo two to the sole bit. Applying that permutation twice restores every basis label, so its matrix square—and consequently its bundled unitary square—is exactly the identity.

4. **`Gates.lean:282` · `Gate.Z_mul_Z`.**
   `Z` is diagonal with entries `1` and `−1`. Both entries square to one, giving the identity matrix with no residual phase.

5. **`Gates.lean:290` · `Gate.X_ne_one`.**
   The matrix entry with output label `1` and input label `0` is one for `X`. The corresponding identity entry is zero, so the matrices and bundled gates differ.

6. **`ApplyOn.lean:185` · `applyOn_of_fin_zero`.**
   An embedding from `Fin 0` has empty image, so `AgreeOff w y x` requires equality at every global wire, equivalently `y = x`. Both restricted local labels are the unique empty function `Fin.elim0`, making every diagonal entry `U Fin.elim0 Fin.elim0` and every off-diagonal entry zero. This remains valid at `n = 0` and for arbitrary, nonunitary `U`.

7. **`ApplyOn.lean:221` · `applyOn_wires20_CNOT_mulVec_basis`.**
   Restriction along `wires20` presents CNOT with the ordered local input `(x 2, x 0)`. Its permutation preserves the first component and replaces the second by `x 0 + x 2`, while `AgreeOff` preserves global wire `1`. Thus the unique output is precisely the stated `Function.update`, with amplitude one.

8. **`Protocols.lean:83` · `no_cloning_of_overlap`.**
   Unitarity preserves the input inner product, which equals `⟨ψ, φ⟩` because the blank basis ket is normalized. The proposed outputs have inner product `conj(c₁) c₂ ⟨ψ, φ⟩²`; taking absolute values and using the phase hypotheses gives `t = t²`. This contradicts `0 < t < 1`, exactly the two stated overlap hypotheses.

9. **`Protocols.lean:98` · `no_cloning` — changed.**
   `Nontrivial d` supplies distinct basis labels, whose first basis ket and normalized equal superposition have overlap modulus `1/√2`. A purported universal cloner supplies the two output phases required by the preceding theorem. That theorem then gives a contradiction, independently of the chosen blank label `e`.

10. **`Protocols.lean:111` · `no_exact_cloning`.**
    Apply the proposed copying property to the basis ket at `e` and its negative, both normalized. Linearity makes their outputs negatives of each other, whereas their tensor squares are identical. The resulting equality between the basis vector at `(e,e)` and its negative contradicts its nonzero amplitude, including on a one-element basis.

11. **`Protocols.lean:258` · `superdenseState_vec`.**
    Evaluating the encoder `X^{b₁} Z^{b₀}`, followed by CNOT and Hadamard decoding, gives `|00⟩`, `|01⟩`, `|10⟩`, and `−|11⟩` for the four respective messages. These are exactly the four cases of the multiplier `(-1)^(b₀.val * b₁.val)`. The new statement therefore records the actual vector, including the sign omitted by the probability theorem.

12. **`GapP.lean:113` · `gap_boolVerifier_int`.**
    A Boolean verifier never abstains, so its accepting and rejecting seed counts sum to `2^m`. Their integer difference is therefore twice the accepting count minus `2^m`, with subtraction performed in `ℤ`. At `m = 0`, the unique empty seed gives either `1` or `−1`, as required.

13. **`GapP.lean:122` · `abs_gap_le`.**
    Accepting and rejecting seeds are disjoint subsets of the `2^m` available seeds. Their difference lies between `−2^m` and `2^m`, even when some seeds abstain. This proves the absolute-value bound, including `m = 0`.

14. **`Inclusions.lean:94` · `inPP_polyTimeModel_headD`.**
    Use the Boolean verifier that returns `x.headD false`, ignoring its random string, and choose the zero-length schedule. Its acceptance probability is one exactly on the stated language and zero elsewhere. Decoding the input component and inspecting its first bit is polynomial-time; its accepting predicate and complement supply the two languages required by `polyTimeModel.Eff`, including for the empty input.

## The four other new theorem statements

Their proof scripts were not reviewed.

| Declaration | Statement check |
|---|---|
| `qubitEquivBool_zero` | Correct: the bridge sends `0` to `false`. |
| `qubitEquivBool_one` | Correct: the bridge sends `1` to `true`. |
| `Ket.nonempty_reg_zero` | Correct: the delta ket at the unique empty register label witnesses nonemptiness. Its use of `Ket.basis` explains the inherited `sorryAx`. |
| `wires20_apply` | Correct: it exposes the embedding’s defining function, `![2, 0]`. |

## New adversarial instantiations aimed at the repairs

The following include fresh tests of the strengthened specifications, rather than just repetitions of the round-1 counterexamples.

| Test | Instantiation and result |
|---|---|
| Complex overlap | Take `ψ = (1,i)/√2` and `φ = (1,1)/√2`. Their overlap is `(1−i)/2`, with modulus `1/√2`; output phases cannot remove the contradiction between that modulus and its square. This tests conjugation and phase handling together. |
| Same ray, different representatives | On a singleton basis, take `ψ = \|e⟩` and `φ = i\|e⟩`. Identity copies these up to phases `1` and `−i`. Their overlap modulus is one, so the repaired two-state theorem correctly excludes them. |
| Orthogonal endpoint | On a two-element basis with blank `\|0⟩`, CNOT copies both `\|0⟩` and `\|1⟩`. Their overlap is zero, so the strict lower overlap bound is necessary. |
| Erasure in the cited gate set | Prepare a Bell pair and erase one qubit. The remaining density matrix is `I/2`, of rank two; this exposes the purification qualification needed in the GapP prose. |
| Zero contribution in commutation | Set one placed matrix to zero and the other to `Z`, on disjoint wires. The products commute, but every intermediate contribution vanishes. This produces finding 2. |
| Short seed without abstention | Set `M ≡ some true`, `p \|x\| = 2`, and `m = 1`. The coin-fill formula still holds, producing finding 3. With the always-abstaining verifier at the same lengths, it fails. |
| Zero-wire nonunitary and singular operators | Use the scalar matrices `[2+3i]`, `[0]`, and `[−i]`, at `n = 0,1,3`. All nine placements equal the corresponding scalar times identity. |
| Reversed placement and exact phase | Check all eight inputs for `wires20` CNOT and all four superdense messages. Both formulas hold, including `011 ↦ 111` and the negative output vector for message `11`. |

Independent executable checks also covered **6,654** accept/reject/abstain tables and **278** Boolean tables at seed lengths `0–3`, plus **31** first-bit-language inputs at zero seed length. All assertions passed. Counting used exact integers and rational numbers; complex matrix checks used tolerance `10⁻¹²`. These computations support the arguments, not kernel verification.

## Answers to the seven specific questions

**1. No-cloning.** All three statements are true as literally stated. The sum `∑ₓ star(ψ.vec x) * φ.vec x` conjugates the first argument, exactly matching [de Wolf, Appendix A.3](https://arxiv.org/pdf/1907.09415v6), printed p.194. The changed universal theorem expresses the phase-permitting physical obstruction requested in round 1. Dropping `Nontrivial` from `no_exact_cloning` is correct: its phase-based contradiction needs only the supplied `e : d`. On an empty basis, no such `e` can be supplied.

The formal blank is a computational-basis ket. This is sufficient for the stated obstruction: any fixed normalized pure blank can be reached from it by a unitary on the blank register. The declaration itself does not state the more general channel-with-environment formulation.

**2. GapP module explanation.** The integer-numerator account is correct for the intended computational-basis input and unitary purification. Each output amplitude has a Gaussian-integer numerator divided by `(√2)^h`; squaring its modulus gives an integer numerator over `2^h`, and summing accepting outcomes preserves that denominator. Polynomial size and uniform generation remain necessary for the later claim that the resulting numerator function belongs to GapP. Finding 1 requests only that the paragraph explicitly identify the purification already specified by FD-4.

**3. Drift.** The claim is confirmed for the supplied snapshots, with a stronger check than the signature-only script:

| Comparison | Result |
|---|---|
| Explicit declarations | `194 → 212` |
| Added | 18 |
| Removed | 0 |
| Existing signatures changed | Only `no_cloning` |
| Other existing declaration bodies changed after removing comments/whitespace | None |
| Changed audited Lean files | 8 |
| Git textual diff statistics | **203 insertions, 19 deletions**, matching the pack |
| Existing definition bodies | All unchanged |
| Supplied received foundation files and `TCSlib.lean` | Unchanged |

The full diff contains the declared additions, documentation repairs, and facade imports. The drift script alone would not establish definition-body stability because it stops at `:=`; the independent body comparison supplies that missing check.

**4. New sanity statements.** They are true and test the intended distinctions. In particular, `Fin.elim0` names the sole basis label of `Reg 0`; it does not denote an empty matrix. The reversed CNOT theorem tests ordered wire placement, and the first-bit PP language is nontrivial because it contains `[true]` and excludes `[]`. The exact superdense theorem correctly includes the sign.

**5. Deferrals.** None should hold the P1 gate.

| Deferred proposal | Assessment |
|---|---|
| Q0.10: standard GapP bridge | Appropriate to defer while explicitly distinguishing mathematical correspondence from a formal bridge theorem. |
| Q0.11: AB09 tie variant | Appropriate: the convention difference is disclosed and the integer-shift argument is correct. |
| Q1.7: teleportation with an external reference | Appropriate: the current declarations specify pure-input correctness, not the stronger reference-system statement. |
| Empty-seed regression lemmas | Useful additions at fill time; current theorem guards already protect the relevant identities. |
| Product-basis probability factorization | Useful interface lemma, but no audited P1 statement depends on having it separately named. |

**6. Facade.** Importing all five modules directly is consistent with the stated repository lint rule and precedent. Those modules were already transitively imported through `Quantum.Basic`, so this repairs facade conformance rather than recovering previously inaccessible declarations.

**7. Anything else.** I found no further mathematical regression or unacknowledged expansion of duplication debt. The supplied sweep covers 14 modules and reports **85 direct admissions**. The 246-row axiom census is internally consistent: **123 clean constants**, **104 sorry-dependent theorem constants**—85 direct and 19 inherited—and **19 sorry-dependent definitions**, with no listed axioms beyond the four reported in the pack. These are checked execution records supplied by the maintainer, not a fresh elaboration result from this audit.
