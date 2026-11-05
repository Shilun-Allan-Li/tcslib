## ===== briefs/pass-shelat-ch5-8/gates/05-pac/pack-r3.md =====

# Gate 05 (Pass–shelat ch. 5–8, S3d layer 1), round 3: closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194)
at its head `f0385dac9ff477ef2debff7336d454b1a28b8818`, after the round 2 repair (one commit on
`6b781240`, docstrings only). Round 2's findings (`gate05-pac-r2-findings.md`), the round 2
resolutions (`resolutions-r2.md`), the repair diff (`evidence-r3/repair.diff.txt`), the changed files
and the corrected design note are in the bundle. The deliverable is **`gate05-pac-r3-findings.md`**.

## Brief for the auditor

1. For each of R2-1, R2-2, R2-3 and the round 1 items F5, F6, F11 and F14, say whether the
   resolution is adequate: **fixed**, **recorded**, or **not resolved** (say why).
2. Read the changed docstrings afresh: is every statement about [KV94] and [SSBD14] accurate as
   worded, and does each docstring say exactly what its Lean statement says? Look for regressions.
   No definition or statement changed (the repair diff shows docstrings and comments only).

**Attestations** (maintainer): the four changed modules re-checked in import order at `f0385dac`:
all pass, no diagnostics; `style_lint` 0 findings in each.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per item: `R2-1: fixed / recorded / not resolved — <reason>` (also R2-2, R2-3, F5,
F6, F11, F14). Severity guide: blocker, major, minor, note (as in rounds 1–2). The gate closes at
**0 blockers and 0 majors**.

## ===== gate05-pac-r2-findings.md =====

# Gate 05, round 2: external audit findings

Audited [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194) at `6b781240bc438a103291c74b2ffefaa910f1a70d`, against round 1 at `44d27f39c233849a3a30a117bf15434610e485e9`. Date: 2026-11-05.

**DO NOT CLOSE: 0 blockers, 1 major, 2 minors.** The new theorem is correct and matches its docstring. The original `PACLearnable` problem is repaired. However, the rewritten weak-learning source comparison imports an incorrect assertion from round 1: KV94 §4.1 does not require the original weak learner to attain every confidence level. That distinction matters to the advertised use of the prediction bridge. Two documentation/record discrepancies also remain.

These counts cover current actionable findings; accepted deferrals are identified separately below.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | **major** | `TCSlib/LearningTheory/PAC/Defs.lean:192` and `:212` · `WeakLearnsUnder`, `WeakLearns`; `PAC/Prediction.lean:189` · `not_weakLearnsUnder_of_predictAdv_le` | The new prose incorrectly attributes an arbitrary-confidence requirement to KV94 §4.1 and treats fixing confidence as a relaxation of that requirement for the same learner. Consequently, “apply this at some `δ < γ' − γ`” omits a necessary change of learner when starting from that source's definition. | KV94 §4.1, p. 74, allows a good hypothesis with probability only `1/q(n, size(c))`, with edge `1/p(n, size(c))`. Confidence amplification is a separate construction in §4.2, pp. 76–77. The learner below meets the former guarantee, has prediction advantage zero, and fails the small-`δ` guarantee. The Lean implication itself remains true. | Describe these predicates as fixed-parameter accuracy/confidence conditions, and distinguish the confidence-amplified convention from the original definition. For the source-level implication, explicitly require a confidence-boosted learner, its new sample count and runtime, and any loss of edge before applying the bridge. Record that obligation for layer 2; no strengthening of the current Lean theorem is required. Comparisons must also use the learner's certified edge and sufficient sample count. |
| R2-2 | **minor** | `design/S3d-pac-learning.md:46` · Layer 1, bridge bullet; `resolutions-r1.md` · F5, F11 | The design-note parts of F5/F11 remain uncorrected despite the resolution entries saying “Fixed.” | The note still says `γ' > γ` “at a stated `δ`” and calls the step “Markov on the error.” The actual sufficient condition is `γ + δ < γ' ≤ ½`. The bound comes from splitting the expectation over the accuracy event and its complement. At `δ = ½`, the learner below has zero prediction advantage and satisfies `WeakLearnsUnder` with positive edge. | Synchronize the design note with the theorem's condition; describe the expectation split; amend the resolution entries. Preserve R2-1's separate confidence-amplification obligation. |
| R2-3 | **minor** | `resolutions-r1.md:31` · F14; `InformationTheory/Samples.lean:36`, `:136` · references, `iid` | The record identifies the wrong citation as the one retained. | The resolution says `[SSBD14, §2.3.1]` stays. Both actual citations remain `[SSBD14, §3.1]`. Checking the book resolves the underlying uncertainty: §2.3.1 introduces the product-sampling notation, while §3.1, Definition 3.1, explicitly uses i.i.d. samples. Thus the retained §3.1 citation is defensible; the record is inaccurate. | Correct the record to say §3.1 was retained and verified. Adding §2.3.1 as the more direct location is optional. |

### R2-1: source distinction and counterexample

The relevant source condition is

\[
\Pr[\operatorname{err}_D(h,c)\le \tfrac12-1/p(n,\operatorname{size}(c))]
\ge 1/q(n,\operatorname{size}(c)).
\]

The repair instead attributes a guarantee for every failure probability `δ` to the original learner. This is not the same per-learner condition. KV94's subsequent confidence amplification can justify an implication between existence notions, but it constructs another learner. The primary text is [KV94, §§4.1–4.2, pp. 74, 76–77](https://www.scribd.com/document/932325987/An-Introduction-to-Computational-Learning-Theory), consulted in an online reproduction of the book.

Here is an exact counterexample to the asserted per-learner comparison. Take the two constant concepts on any nonempty finite domain, one example, and a fair Boolean coin. The learner outputs the observed label everywhere on one coin outcome and its complement everywhere on the other. For either target and every distribution,

\[
\Pr[\operatorname{err}=0]=\Pr[\operatorname{err}=1]=\tfrac12.
\]

Therefore

\[
\Pr[\operatorname{err}\le\tfrac14]=\tfrac12,\qquad
\operatorname{predictSuccess}=\tfrac12,\qquad
\operatorname{predictAdv}=0.
\]

This efficient learner meets the source condition with constant polynomials `p = 4`, `q = 2`. Nevertheless, at `γ' = ¼`, `δ = ⅛`,

\[
\tfrac12 < 1-\delta=\tfrac78,
\]

so it does not satisfy the high-confidence predicate. This is fully consistent with the Lean theorem, whose hypotheses hold with `γ = 0`. It demonstrates why that theorem cannot directly refute the original weak-learning guarantee of the same learner.

The repair followed round 1's explicitly memory-based source advice here; that advice was incorrect. This finding does not dispute the intended cryptographic hardness result. It identifies the missing source-to-formalization step.

## Round 1 resolution ledger

F1: **fixed** — `PACLearnable` and `pacLearnable_iff` are removed. The surviving predicates concern specified learners and parameters; the facade and prediction-module prose agree. SSBD14 is no longer assigned a polynomial sample requirement. The finite-domain sample bound is valid information-theoretically, as checked below.

F2: **fixed** — The four predicates declare unrestricted parameters and correctly qualify the listed degeneracies, including the necessary `δ ≥ 0` and `δ < 1` conditions. The negative-accuracy witness is identified as out of range. The new theorem supplies an actual in-range witness.

F3: **fixed** — Improper hypotheses are explicitly declared in the module deviation and the `PACLearns` docstring. The comparison with the cited preliminary KV94 definition and SSBD14 Definition 3.1 is correct.

F4: **fixed** — The finite uniform coin model, its coverage of bounded-time fair-coin algorithms, and its inability to implement irrational conditional mixing exactly are declared. The bounded-time qualification matters; this is not a characterization of every randomized algorithm.

F5: **not resolved** — The numerical confidence condition is now correctly emphasized in the Lean documentation, but the source-level application has R2-1's gap, and the design-note correction requested in round 1 is absent (R2-2).

F6: **not resolved** — The fixed-distribution attribution and fixed real edge/confidence are stated, but the newly added comparison to KV94 §4.1 is materially inaccurate (R2-1). `PACLearnsUnder` itself is correctly described.

F7: **fixed** — `predictSuccess` declares the uniform independent-point reading and permits collisions; `predictAdv` explicitly declares the two-sided reading. These are compatible with the supplied PS10 page; see the source check below.

F8: **fixed** — All four remaining predicate `_iff` docstrings state their formulas; the fifth theorem was removed. The three additional equation-docstring improvements also match their formulas.

F9: **recorded** — The import through `Extractors` remains. G5-2 in the supplied resolutions explicitly defers moving `probTrue` to a follow-up PR to `main`. Accepted as recorded debt, not as an implemented refactor; the separate queue was not supplied or independently verified.

F10: **recorded** — The previous no-duplication observation is retained. The repair changes no retained executable declaration and adds one self-contained non-vacuity proof; no new duplication requiring action was identified. This is not a fresh repository-wide duplication certification.

F11: **not resolved** — `Samples.lean` now accurately says that no lower bound on the function is needed. The requested correction to the design note's “Markov” description remains absent (R2-2).

F12: **fixed** — The prediction-module summary now includes `ε ≥ 0` and the weak-edge upper bound. The optional sharper bound and one-sided variant remain unimplemented, which is acceptable; they were not required fixes.

F13: **recorded** — The `iid` decomposition/marginal API remains deferred until needed. No current statement depends on such a lemma.

F14: **not resolved** — The unused Vad12 reference is removed and the retained source location is now verified, but the resolution entry misidentifies that location (R2-3).

F15: **recorded** — The new log explicitly names all four changed modules. The declaration counts and absence of explicit `sorry` agree with the packet; elaboration, lint and axiom results remain maintainer/worker attestations. No root-module build or independent axiom rerun is asserted here.

F16: **fixed** — I read and visually checked the attached PS10 book p. 179 (PDF p. 191). Its wording does not require the challenge to be distinct from training examples. The uniform independent reading is now declared on the relevant definition.

## New theorem: independent restatement and verification

`TCSlib/LearningTheory/PAC/Defs.lean:277`, `not_pacLearnsUnder_const_pair`, says:

For every finite nonempty coin type `ρ`, every distribution `D` on `Unit`, every learner

\[
L:(\operatorname{Fin}0\to\operatorname{Unit}\times\operatorname{Bool})
\to\rho\to\operatorname{Unit}\to\operatorname{Bool},
\]

and all real `ε < 1`, `δ < ½`, the learner cannot meet the PAC accuracy/confidence guarantee for both constant targets with zero examples. More explicitly, it asserts

\[
\neg\Bigl(\forall b:\operatorname{Bool},\quad
1-\delta\le
\operatorname{accuracyProb}\ D\ (\lambda\_ . b)\ 0\ L\ \varepsilon\Bigr).
\]

**The statement matches the complete docstring and its proof sketch.** It is a sample-size impossibility for a particular class, not a claim that the class is unlearnable.

1. There is a unique empty labelled sample, denoted `s∅`; both targets give that sample. Normalization on the singleton domain gives `D(()) = 1`.
2. For each coin `r` and target bit `b`,

   \[
   \operatorname{err}_D(L(s_\varnothing,r),\lambda\_.b)
   =\begin{cases}
   0,&L(s_\varnothing,r)(())=b,\\
   1,&L(s_\varnothing,r)(())\ne b.
   \end{cases}
   \]

   Since `ε < 1`, accuracy implies agreement with `b`. Thus, for each coin, at most one of the two accuracy events occurs. This remains true when `ε < 0` (neither occurs).
3. Averaging the two indicators over the common sample/coin law gives

   \[
   \operatorname{accuracyProb}\ D\ (\lambda\_.\mathrm{true})\ 0\ L\ \varepsilon
   +\operatorname{accuracyProb}\ D\ (\lambda\_.\mathrm{false})\ 0\ L\ \varepsilon
   \le 1.
   \]

4. Learning both targets would instead give

   \[
   1<2(1-\delta)\le
   \operatorname{accuracyProb}\ D\ (\lambda\_.\mathrm{true})\ 0\ L\ \varepsilon
   +\operatorname{accuracyProb}\ D\ (\lambda\_.\mathrm{false})\ 0\ L\ \varepsilon
   \le1,
   \]

   a contradiction.

The hypotheses have the intended force. Taking `ε = δ = ¼` lies inside both cited sources' parameter ranges. At `δ = ½` and `0 ≤ ε < 1`, a learner outputting a fair coin learns both targets, so the confidence inequality must be strict. At `ε = 1`, every hypothesis is accurate, so the accuracy inequality must also be strict. One labelled example suffices to learn this class exactly.

## Other changed-surface and source checks

- **Finite-domain consistency bound.** For a nonempty class, its set of distinct concepts has size at most `2^|X|`. A fixed hypothesis of error greater than `ε` is consistent with `m` independent examples with probability at most `exp(−mε)`. The union bound therefore gives

  \[
  \Pr[\text{some consistent hypothesis has error}>\varepsilon]
  \le 2^{|X|}e^{-m\varepsilon}\le\delta
  \]

  whenever `ε, δ ∈ (0,1)` and `m ≥ (|X| ln 2 + ln(1/δ))/ε`. The empty class is vacuous. This validates the revised mathematical justification, with no uniform computational-efficiency conclusion as the domain varies.
- **Parameter cases.** The listed cases follow from `0 ≤ accuracyProb ≤ 1` and from error lying in `[0,1]`. For weak learning, substitute `ε = ½ − γ`. Empty `I` makes the target quantifier vacuous; empty `X` makes the distribution-free quantifier vacuous. These claims are correctly separated in the repaired docstrings.
- **PS10 fidelity.** The supplied page uses a random index, labelled examples, and a new test sample; it does not specify their full joint law. The independent uniform completion is explicitly disclosed. Uniformity is over indices, including duplicate concepts. The source's success language is one-sided; the formal absolute advantage is a declared reformulation. At the level of all efficient predictors, complementing the output relates the two sides. No same-predictor implication from a one-sided upper bound to an absolute upper bound is being assumed.
- **Other references.** I checked [KV94 §1.2.1, Definition 1](https://www.jeffreyheinz.net/classes/18S/materials/Kearns-Vairani-1994-Introduction-to-Computational-Learning-Thoery-Ch01.pdf) and [SSBD14 §§2.3.1, 3.1](https://pzs.dstu.dp.ua/DataMining/bibl/understanding-machine-learning-theory-algorithms.pdf). Their preliminary PAC requirements support the declared proper/improper distinction and parameter ranges. Ordinary PAC learnability should be distinguished from efficient PAC learnability when reading the module's summary; its finite-class argument establishes the former.

## Evidence and limits

- Read all 11 bundle sections. Observed bundle SHA-256: `3e5dd418f21a3df7cab2054cf16ce2e7977201788436796c8ef3b870434cf73f`. Attached PDF SHA-256: `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.
- The extracted round 1 findings have SHA-256 `06adae4b5571db4b84c221eeb838f50e9ba5b21dbc89e340529907ed54ca2f16`, matching the resolution record.
- Independently fetched the specified GitHub commit and all four changed Lean files. Their complete contents and Git blob hashes match the bundle; every supplied repair hunk matches the fetched commit patch.
- Reversed the repair locally and compared executable text after removing comments and normalizing whitespace. Apart from deleting `PACLearnable`/`pacLearnable_iff` and adding `not_pacLearnsUnder_const_pair`, retained definitions, theorem statements and proof bodies are unchanged. No logical regression was identified in the retained Lean surface.
- Counted **13 definitions and 38 theorems**: theorem counts `13 + 14 + 11`. No explicit `sorry`, `admit`, `sorryAx` or new axiom declaration occurs in the four changed files.
- Inspected the new proof and independently verified its mathematics above. Exact rational checks of the zero-example boundaries and the label-flipping counterexample agree with the calculations; finite enumeration is not the proof.
- Lean and Lake are not installed in this workspace. I did **not** rerun elaboration, lint or `#print axioms`. The packet's execution claims are identified as attestations, not converted into independent verification. This audit does not certify layer 2 or a full-repository dependency closure.

**Notation introduced here:** `s∅` / $s_\varnothing$ is the unique empty labelled sample; `p,q` are the source's polynomial reciprocals of the edge and good-hypothesis probability; `|X|` is the cardinality of the finite domain. Other notation and declaration names retain the bundle's meanings.


## ===== resolutions-r2.md =====

# Gate 05 (PAC layer, #194): round 2 resolutions

- **Round 2:** findings `findings/gate05-pac-r2-findings.md` on #194 at `6b781240`: **1 major (R2-1),
  2 minors (R2-2, R2-3)**; F1 (round 1's major) fixed; F5, F6, F11 and F14 not resolved; the others
  fixed or recorded.
- **Repair:** one commit on #194's branch, `f0385dac9ff477ef2debff7336d454b1a28b8818`, docstrings and
  module docstrings only (the four modules with comments stripped are byte-identical to `6b781240`).
  Maintainer re-check: the four modules pass in import order with no diagnostics; lint 0. Records:
  the S3d design note's bridge bullet and its `PACLearns` argument order (this commit's records
  companion).

| Item | Severity | Resolution |
|---|---|---|
| R2-1 | major | **Fixed.** `WeakLearnsUnder` ("the weak-learning condition under `D`"), `WeakLearns` and `not_weakLearnsUnder_of_predictAdv_le` no longer attribute an arbitrary-confidence requirement to [KV94, §4.1] nor present fixing the confidence as a relaxation for the same learner. They state [KV94, §4.1, p. 74]'s weak learner (success probability `1/q`, edge `1/p`), that it satisfies the predicate at `δ = 1 − 1/q`, that a smaller `δ` is a stronger requirement for the same learner, and that reaching it needs confidence amplification [KV94, §4.2, pp. 76–77], a different learner. `Prediction.lean`'s module docstring gains a "Use in layer 2" paragraph recording that obligation; the `Defs.lean` "Unrestricted parameters" bullet, the main-definition and main-result lines and the `PAC.lean` contents line are aligned; the [KV94] references list §4.1 (p. 74) and §4.2 (pp. 76–77). |
| R2-2 | minor | **Fixed.** `Prediction.lean`'s module docstring states `γ + δ < γ' ≤ ½` and the expectation split (accuracy event, error ≤ `ε`; complement, probability ≤ `δ`, error ≤ 1). The S3d design note's "Markov on the error" sentence is replaced by the same argument and the amplification obligation. |
| R2-3 | minor | **Fixed.** [SSBD14] locations adopted as verified by the auditor: §2.3.1 (product sampling) and §3.1, Definition 3.1 (i.i.d. examples), in `Samples.lean`'s references and `iid`'s docstring; the unverified notation claim `S ~ D^m` dropped. |
| F5, F6 | (round 1) | **Fixed by R2-1** (the [KV94, §4.1] comparison corrected); **amends** `resolutions-r1.md`, which marked them fixed in round 1. |
| F11 | (round 1) | **Fixed in round 2** with R2-2 (the design note's sentence); amends round 1's "fixed". |
| F14 | (round 1) | **Fixed in round 2:** [SSBD14, §3.1] retained and verified by the round 2 auditor (Def 3.1 uses i.i.d. samples); [SSBD14, §2.3.1] (product sampling) added. |
| M10 (review, round 1) | minor | **Fixed:** the design note's `PACLearns` argument order is the code's, `C m L ε δ`. |

## ===== evidence-r3/repair.diff.txt =====

diff --git a/TCSlib/InformationTheory/Samples.lean b/TCSlib/InformationTheory/Samples.lean
index a416dd85..668b9c31 100644
--- a/TCSlib/InformationTheory/Samples.lean
+++ b/TCSlib/InformationTheory/Samples.lean
@@ -34,7 +34,8 @@ an iterated expectation.
 ## References
 
 * [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
-  Algorithms*, Cambridge University Press, 2014, §3.1 (the i.i.d. sample `S ~ D^m`).
+  Algorithms*, Cambridge University Press, 2014, §2.3.1 (product sampling) and §3.1,
+  Definition 3.1 (i.i.d. examples).
 -/
 
 namespace TCSlib.InformationTheory
@@ -133,7 +134,8 @@ theorem expect_le_add_of_le_one (p : FinDist α) {f : α → ℝ} (hf : ∀ a, f
 /-! ### Independent samples -/
 
 /-- **`m` independent samples** of `p`: the distribution on `Fin m → α` with
-`Pr[s] = ∏ j, p (s j)` ([SSBD14, §3.1], `S ~ D^m`). -/
+`Pr[s] = ∏ j, p (s j)`: the product sampling of [SSBD14, §2.3.1], used for the i.i.d. examples
+of [SSBD14, §3.1, Def 3.1]. -/
 def iid (p : FinDist α) (m : ℕ) : FinDist (Fin m → α) where
   prob s := ∏ j, p (s j)
   nonneg s := Finset.prod_nonneg fun j _ => p.nonneg (s j)
diff --git a/TCSlib/LearningTheory/PAC.lean b/TCSlib/LearningTheory/PAC.lean
index 94807ae1..ae7e3376 100644
--- a/TCSlib/LearningTheory/PAC.lean
+++ b/TCSlib/LearningTheory/PAC.lean
@@ -21,8 +21,9 @@ bridge to PAC learning.
 * `TCSlib.LearningTheory.PAC.Defs`: error, labelled samples, PAC, weak and fixed-distribution
   learning, for a given learner at fixed parameters.
 * `TCSlib.LearningTheory.PAC.Prediction`: the prediction game; success `= 1 − E[err]`, so
-  a small prediction advantage rules out weak learning under the uniform distribution, for that
-  learner, at confidence below the gap.
+  a small prediction advantage rules out the weak-learning condition under the uniform
+  distribution, for that learner, at a confidence below the gap (for a weak learner of
+  [KV94, §4.1], only after confidence amplification, [KV94, §4.2], which changes the learner).
 
 ## References
 
diff --git a/TCSlib/LearningTheory/PAC/Defs.lean b/TCSlib/LearningTheory/PAC/Defs.lean
index 00f04897..4d939688 100644
--- a/TCSlib/LearningTheory/PAC/Defs.lean
+++ b/TCSlib/LearningTheory/PAC/Defs.lean
@@ -35,9 +35,11 @@ independent examples, and PAC, weak and fixed-distribution learning.
   learner's `m`, `ε`, `δ` (`Prediction.lean`; for efficient learners, layer 2 and
   [PS10, Thm 179.1]). This is faithful: a source learner run on `m ≥ m_H(ε, δ)` examples is
   such an `L`.
-- **Unrestricted parameters.** `ε`, `δ` and the weak-learning edge `γ` are arbitrary reals, where
-  the sources take `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`) and `γ > 0`. The docstrings of the
-  predicates list the degenerate cases.
+- **Unrestricted parameters.** `ε`, `δ` and the weak-learning edge `γ` are arbitrary reals. For
+  PAC learning the sources take `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`). The weak learner of
+  [KV94, §4.1, p. 74] has the edge `1/p(n, size(c))` and succeeds with probability
+  `1/q(n, size(c))`, which is the confidence `δ = 1 − 1/q(n, size(c))` here. The docstrings of
+  the predicates list the degenerate cases.
 - **Improper hypotheses.** A learner may output any `X → Bool` (representation-independent
   learning). [KV94, §1.2.1] requires `h ∈ C`; [SSBD14, Def 3.1] does not. A refutation is
   stronger without the restriction.
@@ -57,8 +59,9 @@ independent examples, and PAC, weak and fixed-distribution learning.
   the learner's hypothesis has error at most `ε`.
 * `PAC.PACLearnsUnder D C m L ε δ`, `PAC.PACLearns C m L ε δ`: the learner `L` PAC-learns `C`
   under a fixed distribution and under every distribution, at fixed `m`, `ε`, `δ`.
-* `PAC.WeakLearnsUnder`, `PAC.WeakLearns`: weak learning at a fixed edge `γ`, accuracy `½ − γ`
-  [KV94, §4.1].
+* `PAC.WeakLearnsUnder`, `PAC.WeakLearns`: the accuracy/confidence condition at accuracy
+  `½ − γ` (edge `γ`) and confidence `δ`, at fixed `m`, `γ`, `δ`; their docstrings compare it with
+  weak learning in [KV94, §4.1].
 
 ## Main results
 
@@ -75,7 +78,8 @@ independent examples, and PAC, weak and fixed-distribution learning.
 ## References
 
 * [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
-  1994, §1.2 (PAC learning) and §4 (weak learning).
+  1994, §1.2 (PAC learning), §4.1 (weak learning, p. 74) and §4.2 (confidence amplification,
+  pp. 76–77).
 * [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
   Algorithms*, Cambridge University Press, 2014, ch. 3 (Definition 3.1).
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
@@ -189,12 +193,20 @@ def PACLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ
 theorem pacLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
     (ε δ : ℝ) : PACLearns C m L ε δ ↔ ∀ D, PACLearnsUnder D C m L ε δ := Iff.rfl
 
-/-- **Weak learning under `D`** [KV94, §4.1], by the learner `L` at fixed `m`, `γ`, `δ`: PAC
-learning under `D` with accuracy `½ − γ`, a hypothesis better than a fair coin by the edge `γ`.
-[KV94] asks for this under every distribution, at an edge `γ = 1/p(n, size(c))`, and for every
-confidence `δ`, in time polynomial in `1/δ`; here `D`, the real edge `γ` and the confidence `δ`
-are fixed. Each relaxation makes the predicate weaker, so a refutation for a given learner is
-stronger.
+/-- **The weak-learning condition under `D`**, for the learner `L` at fixed `m`, `γ`, `δ`: with
+probability at least `1 − δ` over `m` examples from `D` labelled by `C i` and the learner's coins,
+the hypothesis has error at most `½ − γ` under `D`, so it beats a fair coin by the edge `γ`. This
+is `PACLearnsUnder` at accuracy `½ − γ`, an accuracy/confidence condition at fixed parameters.
+
+**Comparison with [KV94, §4.1, p. 74].** There a weak learner must, under every distribution,
+output with probability at least `1/q(n, size(c))` a hypothesis of error at most
+`½ − 1/p(n, size(c))`, for polynomials `p` and `q`. Run on a sufficient sample count `m`, such a
+learner satisfies this predicate at its certified edge `γ = 1/p(n, size(c))` and the confidence
+`δ = 1 − 1/q(n, size(c))`; fixing `D` only weakens that requirement. It need not satisfy the
+predicate at a smaller `δ`: for the same learner, a smaller `δ` is a stronger requirement, not a
+relaxation. Asking a weak learner for every `δ` is the confidence-amplified convention, not
+[KV94, §4.1]'s definition: confidence amplification ([KV94, §4.2, pp. 76–77]) builds a different
+learner, with its own sample count, running time and edge.
 
 Only `γ > 0` is weak learning. The parameters are unrestricted reals: every learner satisfies the
 predicate when `δ ≥ 1`, when `γ ≤ −½` and `δ ≥ 0`, or when `I` is empty; no learner satisfies it
@@ -209,11 +221,15 @@ theorem weakLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
     (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
     WeakLearnsUnder D C m L γ δ ↔ PACLearnsUnder D C m L (1 / 2 - γ) δ := Iff.rfl
 
-/-- **Weak learning** [KV94, §4.1], by the learner `L` at fixed `m`, `γ`, `δ`: under every
-distribution `D` on `X`, PAC learning with accuracy `½ − γ` (`WeakLearnsUnder`). [KV94] takes
-the edge `γ = 1/p(n, size(c))` and asks for every confidence `δ`, in time polynomial in `1/δ`;
-here the real edge `γ` and the confidence `δ` are fixed. Each relaxation makes the predicate
-weaker, so a refutation for a given learner is stronger.
+/-- **The weak-learning condition**, for the learner `L` at fixed `m`, `γ`, `δ`: under every
+distribution `D` on `X`, with probability at least `1 − δ` the hypothesis has error at most
+`½ − γ` (`WeakLearnsUnder`), an accuracy/confidence condition at fixed parameters. A weak
+learner of [KV94, §4.1, p. 74], which outputs with probability at least `1/q(n, size(c))` a
+hypothesis of error at most `½ − 1/p(n, size(c))`, satisfies it on a sufficient sample count `m`
+at its certified edge `γ = 1/p(n, size(c))` and the confidence `δ = 1 − 1/q(n, size(c))`. It need
+not satisfy it at a smaller `δ`. Asking for every `δ` is the confidence-amplified convention, which
+concerns a different learner, built by confidence amplification ([KV94, §4.2, pp. 76–77]; see
+`WeakLearnsUnder`).
 
 Only `γ > 0` is weak learning. The parameters are unrestricted reals: every learner satisfies the
 predicate when `δ ≥ 1`, when `γ ≤ −½` and `δ ≥ 0`, or when `I` or `X` is empty; no learner
diff --git a/TCSlib/LearningTheory/PAC/Prediction.lean b/TCSlib/LearningTheory/PAC/Prediction.lean
index d3abde33..016ac0ed 100644
--- a/TCSlib/LearningTheory/PAC/Prediction.lean
+++ b/TCSlib/LearningTheory/PAC/Prediction.lean
@@ -22,11 +22,18 @@ probability of a correct prediction is `1 − err_U(h, C_i)` for the hypothesis
 So the prediction success is `1 − E_{i,s,r}[err_U(L(s, r), C_i)]`
 (`predictSuccess_eq_one_sub_expectedErr`), with no collision issue between the fresh point and
 the sample. A learner that PAC-learns under the uniform distribution with accuracy `ε ≥ 0` and
-confidence `δ` has expected error at most `ε + δ`, hence prediction success at least `1 − ε − δ`.
-So a learner whose prediction advantage is at most `γ` cannot weakly learn under the uniform
-distribution with `γ + δ < γ' ≤ ½` at confidence `δ` (`not_weakLearnsUnder_of_predictAdv_le`).
-This is how layer 2 turns [PS10, Thm 179.1] into "no efficient learner weakly learns the class
-under the uniform distribution" (for each learner, at a confidence below the edge).
+confidence `δ` has expected error at most `ε + δ`: split the expectation over the accuracy event,
+where the error is at most `ε`, and its complement, of probability at most `δ`, where the error is
+at most `1`. Hence its prediction success is at least `1 − ε − δ`, and a learner whose prediction
+advantage is at most `γ` does not satisfy `WeakLearnsUnder` under the uniform distribution at an
+edge `γ'` and confidence `δ` with `γ + δ < γ' ≤ ½` (`not_weakLearnsUnder_of_predictAdv_le`).
+
+**Use in layer 2.** Layer 2 applies this to each efficient learner, turning [PS10, Thm 179.1]
+into a statement at a confidence `δ` below the gap `γ' − γ`. A weak learner of
+[KV94, §4.1, p. 74] need only succeed with probability `1/q(n, size(c))`, that is, at the
+confidence `δ = 1 − 1/q(n, size(c))`. To reach a small `δ` it must first be amplified
+([KV94, §4.2, pp. 76–77]), which gives a different learner; layer 2 must account for that
+learner's sample count, running time and edge before applying the bridge.
 Information-theoretically the class is learnable; the hardness is computational.
 
 **Source notes.** [PS10] leaves the sample distribution and "a new sample" implicit; uniform
@@ -46,9 +53,9 @@ and independent is the reading (design note S3d). "Better than `½ + ε`" is the
 * `PAC.expectedErr_le_of_pacLearnsUnder`, `PAC.one_sub_sub_le_predictSuccess`: PAC learning
   under the uniform distribution with accuracy `ε ≥ 0` gives expected error at most `ε + δ` and
   success at least `1 − ε − δ`.
-* `PAC.sub_le_predictAdv_of_weakLearnsUnder`, `PAC.not_weakLearnsUnder_of_predictAdv_le`: weak
-  learning with `γ' ≤ ½` gives advantage at least `γ' − δ`; so advantage at most `γ` rules out
-  weak learning with `γ + δ < γ' ≤ ½` at confidence `δ`.
+* `PAC.sub_le_predictAdv_of_weakLearnsUnder`, `PAC.not_weakLearnsUnder_of_predictAdv_le`: the
+  weak-learning condition at edge `γ' ≤ ½` and confidence `δ` gives advantage at least `γ' − δ`;
+  so advantage at most `γ` rules it out when `γ + δ < γ' ≤ ½`.
 * `PAC.predictSuccess_coin`: the learner that outputs its coin succeeds with probability exactly
   `½` (non-vacuity).
 
@@ -57,7 +64,7 @@ and independent is the reading (design note S3d). "Better than `½ + ε`" is the
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
   §8.1 (book p. 179).
 * [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
-  1994, §1.2 and §4.
+  1994, §1.2, §4.1 (p. 74) and §4.2 (pp. 76–77).
 * [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
   Algorithms*, Cambridge University Press, 2014, ch. 3.
 -/
@@ -186,12 +193,18 @@ theorem sub_le_predictAdv_of_weakLearnsUnder {C : I → X → Bool} {m : ℕ}
   rw [predictAdv_eq]
   exact le_trans (by linarith) (le_abs_self _)
 
-/-- **Small prediction advantage rules out weak learning**: if the learner's prediction
-advantage is at most `γ`, it does not weakly learn the class under the uniform distribution with
-any `γ' ≤ ½` such that `γ + δ < γ'`, at confidence `δ`. The confidence must be below the gap:
-at a constant confidence such as `δ = ½`, a learner with zero prediction advantage can satisfy
-`WeakLearnsUnder`. To refute weak learning in the sense of [KV94, §4.1], apply this at some
-`δ < γ' − γ`. -/
+/-- **Small prediction advantage rules out the weak-learning condition below the gap**: if the
+learner's prediction advantage is at most `γ`, it does not satisfy `WeakLearnsUnder` under the
+uniform distribution at any edge `γ' ≤ ½` and confidence `δ` with `γ + δ < γ'`. The confidence
+must be below the gap: at a constant confidence such as `δ = ½`, a learner with zero prediction
+advantage can satisfy `WeakLearnsUnder`.
+
+A weak learner of [KV94, §4.1, p. 74] need only succeed with probability `1/q(n, size(c))`, that
+is, at the confidence `δ = 1 − 1/q(n, size(c))`, which in general is not below the gap. Starting
+from that definition, applying this lemma at a small `δ` needs confidence amplification
+([KV94, §4.2, pp. 76–77]), which gives a different learner, with its own sample count, running
+time and edge. It is that learner's certified edge `γ'`, sample count `m` and prediction
+advantage `γ` that enter here. -/
 theorem not_weakLearnsUnder_of_predictAdv_le {C : I → X → Bool} {m : ℕ}
     {L : (Fin m → X × Bool) → ρ → X → Bool} {γ γ' δ : ℝ} (hadv : predictAdv C m L ≤ γ)
     (hlt : γ + δ < γ') (hγ' : γ' ≤ 1 / 2) :

## ===== TCSlib/InformationTheory/Samples.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Extractors

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expectations and independent samples

Two operations on finite distributions that sampling arguments need: the expectation of a
real-valued function, and the distribution of `m` independent samples. With them, a probability
`probTrue` is the expectation of an indicator, and an expectation over a product distribution is
an iterated expectation.

## Main definitions

* `FinDist.expect p f`: the expectation `E_{a ← p}[f a] = ∑ a, p a · f a`.
* `FinDist.iid p m`: `m` independent samples of `p`, a distribution on `Fin m → α`.

## Main results

* `FinDist.probTrue_eq_expect`: a probability is the expectation of an indicator.
* `FinDist.expect_prod`: an expectation over a product distribution is an iterated expectation.
* `FinDist.expect_le_expect`, `FinDist.expect_const`, `FinDist.expect_add`,
  `FinDist.expect_const_mul`, `FinDist.expect_one_sub`: linearity and monotonicity.
* `FinDist.probTrue_not`: the complement rule `Pr[¬D] = 1 − Pr[D]`.
* `FinDist.expect_le_add_of_le_one`: a function with values at most `1` has expectation at most
  `ε + Pr[f > ε]`, for `ε ≥ 0`.

## References

* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, §2.3.1 (product sampling) and §3.1,
  Definition 3.1 (i.i.d. examples).
-/

namespace TCSlib.InformationTheory

open Finset

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Expectation -/

/-- The **expectation** `E_{a ← p}[f a] = ∑ a, p a · f a`. -/
noncomputable def expect (p : FinDist α) (f : α → ℝ) : ℝ := ∑ a, p a * f a

/-- The expectation as a weighted sum: `E_{a ← p}[f a] = ∑ a, p a · f a`. -/
theorem expect_eq (p : FinDist α) (f : α → ℝ) : p.expect f = ∑ a, p a * f a := rfl

/-- The expectation of a constant is the constant: `E_p[c] = c`. -/
theorem expect_const (p : FinDist α) (c : ℝ) : p.expect (fun _ => c) = c := by
  rw [expect_eq, ← Finset.sum_mul, p.sum_prob, one_mul]

/-- The expectation is additive: `E_p[f + g] = E_p[f] + E_p[g]`. -/
theorem expect_add (p : FinDist α) (f g : α → ℝ) :
    p.expect (fun a => f a + g a) = p.expect f + p.expect g := by
  simp only [expect_eq, mul_add, Finset.sum_add_distrib]

/-- The expectation commutes with scaling: `E_p[c · f] = c · E_p[f]`. -/
theorem expect_const_mul (p : FinDist α) (c : ℝ) (f : α → ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  simp only [expect_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The expectation of `1 − f` is `1 − E_p[f]`. -/
theorem expect_one_sub (p : FinDist α) (f : α → ℝ) :
    p.expect (fun a => 1 - f a) = 1 - p.expect f := by
  simp only [expect_eq, mul_sub, mul_one, Finset.sum_sub_distrib, p.sum_prob]

/-- The expectation is monotone: `f ≤ g` pointwise gives `E_p[f] ≤ E_p[g]`. -/
theorem expect_le_expect (p : FinDist α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (p : FinDist α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ p.expect f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (h a)

/-- **A probability is the expectation of an indicator**:
`Pr_{a ← p}[D a] = E_{a ← p}[1_{D a}]`. -/
theorem probTrue_eq_expect (p : FinDist α) (D : α → Bool) :
    p.probTrue D = p.expect (fun a => if D a = true then 1 else 0) := by
  rw [probTrue_eq, expect_eq, Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp

/-- **The complement rule**: `Pr_p[¬D] = 1 − Pr_p[D]`. -/
theorem probTrue_not (p : FinDist α) (D : α → Bool) :
    p.probTrue (fun a => !D a) = 1 - p.probTrue D := by
  rw [probTrue_eq_expect, probTrue_eq_expect, ← expect_one_sub]
  congr 1
  funext a
  cases D a <;> simp

/-- The probability of the always-accepting test is `1`. -/
theorem probTrue_true (p : FinDist α) : p.probTrue (fun _ => true) = 1 := by
  rw [probTrue_eq_expect]
  simpa using p.expect_const 1

/-- **Iterated expectation over a product**:
`E_{(a, b) ← p × q}[f (a, b)] = E_{a ← p}[E_{b ← q}[f (a, b)]]`. -/
theorem expect_prod (p : FinDist α) (q : FinDist β) (f : α × β → ℝ) :
    (p.prod q).expect f = p.expect (fun a => q.expect (fun b => f (a, b))) := by
  simp only [expect_eq, Fintype.sum_prod_type, prod_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **A function with values at most `1` has expectation at most `ε + Pr[f > ε]`**, for
`ε ≥ 0`: on the event `f ≤ ε` it contributes at most `ε`, elsewhere at most `1`. No lower bound
on `f` is needed.

**Proof sketch.** Pointwise `f a ≤ ε + 1_{f a > ε}`, since `f a ≤ 1` and `ε ≥ 0`; take expectations
(`expect_le_expect`, `expect_add`, `expect_const`, `probTrue_eq_expect`). -/
theorem expect_le_add_of_le_one (p : FinDist α) {f : α → ℝ} (hf : ∀ a, f a ≤ 1) {ε : ℝ}
    (hε : 0 ≤ ε) :
    p.expect f ≤ ε + p.probTrue (fun a => !decide (f a ≤ ε)) := by
  have key : ∀ a, f a ≤ ε + (if (!decide (f a ≤ ε)) = true then 1 else 0) := by
    intro a
    by_cases h : f a ≤ ε
    · simp [h]
    · simp [h]
      linarith [hf a]
  calc p.expect f
      ≤ p.expect (fun a => ε + (if (!decide (f a ≤ ε)) = true then 1 else 0)) :=
        p.expect_le_expect key
    _ = ε + p.probTrue (fun a => !decide (f a ≤ ε)) := by
        rw [expect_add p (fun _ => ε), expect_const, probTrue_eq_expect]

/-! ### Independent samples -/

/-- **`m` independent samples** of `p`: the distribution on `Fin m → α` with
`Pr[s] = ∏ j, p (s j)`: the product sampling of [SSBD14, §2.3.1], used for the i.i.d. examples
of [SSBD14, §3.1, Def 3.1]. -/
def iid (p : FinDist α) (m : ℕ) : FinDist (Fin m → α) where
  prob s := ∏ j, p (s j)
  nonneg s := Finset.prod_nonneg fun j _ => p.nonneg (s j)
  sum_prob := by
    have h := Finset.prod_univ_sum (fun _ : Fin m => (univ : Finset α)) (fun _ a => p a)
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    simp only [p.sum_prob, Finset.prod_const_one]

/-- The probability of a sample is the product of the probabilities of its entries:
`Pr_{p^m}[s] = ∏ j, p (s j)`. -/
theorem iid_apply (p : FinDist α) (m : ℕ) (s : Fin m → α) : p.iid m s = ∏ j, p (s j) := rfl

end FinDist

end TCSlib.InformationTheory

## ===== TCSlib/LearningTheory/PAC/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Samples

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PAC learning over a finite domain

Probably approximately correct (PAC) learning in the realizable setting, information-theoretic
(learners are arbitrary functions, with finite random coins): a concept class `C : I → X → Bool`
over a finite domain `X`, the error of a hypothesis under a distribution, labelled samples of `m`
independent examples, and PAC, weak and fixed-distribution learning.

**Conventions.**
- A concept is a function `X → Bool`, and the class is indexed, `C : I → X → Bool`, as in
  [PS10, §8.1] (`{C_i}_{i ∈ I}`).
- A learner with `m` examples and coins `ρ` is a function
  `L : (Fin m → X × Bool) → ρ → (X → Bool)`; its coins are uniform on the finite type `ρ`.
- Distributions are `InformationTheory.FinDist`: real-valued, on a finite type.

**Deviations from [KV94, §1.2.1] and [SSBD14, Def 3.1].**
- **Learners at fixed parameters, not learnability of a class.** `PACLearns C m L ε δ` is the
  condition the sources place on one learner `L` at one sample size `m`, accuracy `ε` and
  confidence `δ`. Their learnability asks for one algorithm that meets it for every
  `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`) on `m ≥ m_H(ε, δ)` examples, for some function `m_H`;
  [KV94] also bounds the running time, and so `m`, by a polynomial in `1/ε`, `1/δ` and the
  instance size. That class-level notion is not defined here: over a finite `X` every class has
  it, since a learner that outputs a concept of the class consistent with its sample succeeds
  once `m ≥ (|X| ln 2 + ln (1/δ)) / ε`. Impossibility is therefore stated per learner, at that
  learner's `m`, `ε`, `δ` (`Prediction.lean`; for efficient learners, layer 2 and
  [PS10, Thm 179.1]). This is faithful: a source learner run on `m ≥ m_H(ε, δ)` examples is
  such an `L`.
- **Unrestricted parameters.** `ε`, `δ` and the weak-learning edge `γ` are arbitrary reals. For
  PAC learning the sources take `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`). The weak learner of
  [KV94, §4.1, p. 74] has the edge `1/p(n, size(c))` and succeeds with probability
  `1/q(n, size(c))`, which is the confidence `δ = 1 − 1/q(n, size(c))` here. The docstrings of
  the predicates list the degenerate cases.
- **Improper hypotheses.** A learner may output any `X → Bool` (representation-independent
  learning). [KV94, §1.2.1] requires `h ∈ C`; [SSBD14, Def 3.1] does not. A refutation is
  stronger without the restriction.
- **Coins.** A learner's coins are uniform on a finite type. This models every fair-coin
  algorithm with bounded running time ([KV94]), and [SSBD14]'s deterministic learners are the
  case `ρ = Unit`. A learner that needs an irrational mixing probability is not of this form. At
  a fixed `D` and an exactly tight `δ` this can matter, so a statement `¬ ∃ ρ L, …` rules out
  fair-coin learners, not every randomized learner.
- **Finite domains.** `X` is a finite type, so the "instance size" of [KV94] is not modelled.
  With `X` empty there is no distribution on `X`, so every PAC statement holds vacuously.

## Main definitions

* `PAC.err D h c`: the error `Pr_{x ← D}[h x ≠ c x]` of `h` against the target `c`.
* `PAC.label c s`: the sample `s` labelled by `c`.
* `PAC.accuracyProb D c m L ε`: the probability, over `m` examples from `D` and the coins, that
  the learner's hypothesis has error at most `ε`.
* `PAC.PACLearnsUnder D C m L ε δ`, `PAC.PACLearns C m L ε δ`: the learner `L` PAC-learns `C`
  under a fixed distribution and under every distribution, at fixed `m`, `ε`, `δ`.
* `PAC.WeakLearnsUnder`, `PAC.WeakLearns`: the accuracy/confidence condition at accuracy
  `½ − γ` (edge `γ`) and confidence `δ`, at fixed `m`, `γ`, `δ`; their docstrings compare it with
  weak learning in [KV94, §4.1].

## Main results

* `PAC.err_nonneg`, `PAC.err_le_one`, `PAC.err_self`, `PAC.err_not`: basic properties; `err_not`
  says the complementary hypothesis has the complementary error.
* `PAC.pacLearns_const`: the constant learner PAC-learns a class with one concept from no
  examples, at every `ε, δ ≥ 0` (non-vacuity).
* `PAC.not_pacLearnsUnder_of_neg`: no learner reaches a negative accuracy with confidence
  `δ < 1` (a witness outside the sources' range).
* `PAC.not_pacLearnsUnder_const_pair`: with no examples, no learner learns the two constant
  concepts on a one-point domain at accuracy `ε < 1` and confidence `δ < ½` (a witness inside
  the sources' range).

## References

* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994, §1.2 (PAC learning), §4.1 (weak learning, p. 74) and §4.2 (confidence amplification,
  pp. 76–77).
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, ch. 3 (Definition 3.1).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1 (book p. 179).
-/

namespace TCSlib.LearningTheory.PAC

open TCSlib.InformationTheory Finset

variable {X I ρ : Type*} [Fintype X]

/-! ### Error and samples -/

/-- The **error** of the hypothesis `h` against the target concept `c` under `D`:
`err_D(h, c) = Pr_{x ← D}[h x ≠ c x]` [KV94, §1.2]. -/
noncomputable def err (D : FinDist X) (h c : X → Bool) : ℝ := D.probTrue fun x => h x != c x

/-- The error is the probability of disagreement: `err_D(h, c) = Pr_{x ← D}[h x ≠ c x]`. -/
theorem err_eq (D : FinDist X) (h c : X → Bool) :
    err D h c = D.probTrue (fun x => h x != c x) := rfl

/-- The error is nonnegative. -/
theorem err_nonneg (D : FinDist X) (h c : X → Bool) : 0 ≤ err D h c := by
  rw [err_eq, FinDist.probTrue_eq]
  exact Finset.sum_nonneg fun x _ => D.nonneg x

/-- The error is at most `1`. -/
theorem err_le_one (D : FinDist X) (h c : X → Bool) : err D h c ≤ 1 := by
  rw [err_eq, FinDist.probTrue_eq, ← D.sum_prob]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun x _ _ => D.nonneg x

/-- The target has error `0` against itself. -/
theorem err_self (D : FinDist X) (c : X → Bool) : err D c c = 0 := by
  rw [err_eq, FinDist.probTrue_eq]
  simp

/-- The complementary hypothesis has the complementary error:
`err_D(¬h, c) = 1 − err_D(h, c)`. -/
theorem err_not (D : FinDist X) (h c : X → Bool) :
    err D (fun x => !h x) c = 1 - err D h c := by
  rw [err_eq, err_eq, ← FinDist.probTrue_not]
  congr 1
  funext x
  cases h x <;> cases c x <;> rfl

/-- The **labelled sample** `((x_j, c(x_j)))_j` of the examples `s` under the target `c`. -/
def label (c : X → Bool) {m : ℕ} (s : Fin m → X) : Fin m → X × Bool := fun j => (s j, c (s j))

omit [Fintype X] in
/-- The `j`-th labelled example is `(s j, c (s j))`. -/
theorem label_apply (c : X → Bool) {m : ℕ} (s : Fin m → X) (j : Fin m) :
    label c s j = (s j, c (s j)) := rfl

/-! ### PAC learning -/

variable [Fintype ρ] [Nonempty ρ]

/-- The **accuracy probability** of the learner `L` with `m` examples: over `m` independent
examples from `D`, labelled by the target `c`, and uniform coins, the probability that the
hypothesis has error at most `ε`. -/
noncomputable def accuracyProb (D : FinDist X) (c : X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε : ℝ) : ℝ :=
  ((D.iid m).prod (FinDist.uniform ρ)).probTrue
    fun sr => decide (err D (L (label c sr.1) sr.2) c ≤ ε)

/-- The accuracy probability is the probability, over examples `s ← D^m` and uniform coins
`r ← ρ`, of the event `err_D(L(s labelled by c, r), c) ≤ ε`. -/
theorem accuracyProb_eq (D : FinDist X) (c : X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε : ℝ) :
    accuracyProb D c m L ε = ((D.iid m).prod (FinDist.uniform ρ)).probTrue
      (fun sr => decide (err D (L (label c sr.1) sr.2) c ≤ ε)) := rfl

/-- **PAC learning under the distribution `D`** (fixed-distribution learning), by the learner `L`
at fixed `m`, `ε`, `δ`: for every concept `C i` of the class, with probability at least `1 − δ`
over `m` examples from `D` labelled by `C i` and the learner's coins, the hypothesis has error at
most `ε` under `D`. This is the fixed-distribution variant of [KV94, §1.2.1] /
[SSBD14, Def 3.1] (the case [PS10, §8.1] needs); it is weaker than distribution-free learning.

The parameters are unrestricted reals; the sources take `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`).
Outside that range the predicate is degenerate: every learner satisfies it when `δ ≥ 1`, when
`ε ≥ 1` and `δ ≥ 0`, or when `I` is empty; no learner satisfies it when `I` is nonempty and
either `δ < 0`, or `ε < 0` and `δ < 1`. -/
def PACLearnsUnder (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) : Prop :=
  ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε

/-- `PACLearnsUnder D C m L ε δ` holds iff `1 − δ ≤ accuracyProb D (C i) m L ε` for every
index `i`. -/
theorem pacLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) :
    PACLearnsUnder D C m L ε δ ↔ ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε := Iff.rfl

/-- **A PAC learner at fixed parameters** [KV94, §1.2.1], [SSBD14, Def 3.1]: for every
distribution `D` on `X` and every concept `C i`, with probability at least `1 − δ` over `m`
examples from `D` labelled by `C i` and the learner's coins, the hypothesis has error at most `ε`
under `D`. The sources require this of one algorithm for every `ε, δ` and every large enough `m`.
Here `m`, `ε`, `δ` are fixed, `ε` and `δ` are unrestricted reals, the hypothesis may be any
`X → Bool`, and the coins are uniform on the finite type `ρ` (module deviations).

Outside the sources' range `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`) the predicate is degenerate: every
learner satisfies it when `δ ≥ 1`, when `ε ≥ 1` and `δ ≥ 0`, or when `I` or `X` is empty; no
learner satisfies it when `I` and `X` are nonempty and either `δ < 0`, or `ε < 0` and `δ < 1`. -/
def PACLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) :
    Prop :=
  ∀ D : FinDist X, PACLearnsUnder D C m L ε δ

/-- `PACLearns C m L ε δ` holds iff `PACLearnsUnder D C m L ε δ` holds for every distribution
`D` on `X`. -/
theorem pacLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
    (ε δ : ℝ) : PACLearns C m L ε δ ↔ ∀ D, PACLearnsUnder D C m L ε δ := Iff.rfl

/-- **The weak-learning condition under `D`**, for the learner `L` at fixed `m`, `γ`, `δ`: with
probability at least `1 − δ` over `m` examples from `D` labelled by `C i` and the learner's coins,
the hypothesis has error at most `½ − γ` under `D`, so it beats a fair coin by the edge `γ`. This
is `PACLearnsUnder` at accuracy `½ − γ`, an accuracy/confidence condition at fixed parameters.

**Comparison with [KV94, §4.1, p. 74].** There a weak learner must, under every distribution,
output with probability at least `1/q(n, size(c))` a hypothesis of error at most
`½ − 1/p(n, size(c))`, for polynomials `p` and `q`. Run on a sufficient sample count `m`, such a
learner satisfies this predicate at its certified edge `γ = 1/p(n, size(c))` and the confidence
`δ = 1 − 1/q(n, size(c))`; fixing `D` only weakens that requirement. It need not satisfy the
predicate at a smaller `δ`: for the same learner, a smaller `δ` is a stronger requirement, not a
relaxation. Asking a weak learner for every `δ` is the confidence-amplified convention, not
[KV94, §4.1]'s definition: confidence amplification ([KV94, §4.2, pp. 76–77]) builds a different
learner, with its own sample count, running time and edge.

Only `γ > 0` is weak learning. The parameters are unrestricted reals: every learner satisfies the
predicate when `δ ≥ 1`, when `γ ≤ −½` and `δ ≥ 0`, or when `I` is empty; no learner satisfies it
when `I` is nonempty and either `δ < 0`, or `γ > ½` and `δ < 1`. -/
def WeakLearnsUnder (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) : Prop :=
  PACLearnsUnder D C m L (1 / 2 - γ) δ

/-- `WeakLearnsUnder D C m L γ δ` holds iff `PACLearnsUnder D C m L (½ − γ) δ`: PAC learning
under `D` at accuracy `½ − γ`. -/
theorem weakLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
    WeakLearnsUnder D C m L γ δ ↔ PACLearnsUnder D C m L (1 / 2 - γ) δ := Iff.rfl

/-- **The weak-learning condition**, for the learner `L` at fixed `m`, `γ`, `δ`: under every
distribution `D` on `X`, with probability at least `1 − δ` the hypothesis has error at most
`½ − γ` (`WeakLearnsUnder`), an accuracy/confidence condition at fixed parameters. A weak
learner of [KV94, §4.1, p. 74], which outputs with probability at least `1/q(n, size(c))` a
hypothesis of error at most `½ − 1/p(n, size(c))`, satisfies it on a sufficient sample count `m`
at its certified edge `γ = 1/p(n, size(c))` and the confidence `δ = 1 − 1/q(n, size(c))`. It need
not satisfy it at a smaller `δ`. Asking for every `δ` is the confidence-amplified convention, which
concerns a different learner, built by confidence amplification ([KV94, §4.2, pp. 76–77]; see
`WeakLearnsUnder`).

Only `γ > 0` is weak learning. The parameters are unrestricted reals: every learner satisfies the
predicate when `δ ≥ 1`, when `γ ≤ −½` and `δ ≥ 0`, or when `I` or `X` is empty; no learner
satisfies it when `I` and `X` are nonempty and either `δ < 0`, or `γ > ½` and `δ < 1`. -/
def WeakLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
    Prop :=
  ∀ D : FinDist X, WeakLearnsUnder D C m L γ δ

/-- `WeakLearns C m L γ δ` holds iff `WeakLearnsUnder D C m L γ δ` holds for every distribution
`D` on `X`. -/
theorem weakLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
    (γ δ : ℝ) : WeakLearns C m L γ δ ↔ ∀ D, WeakLearnsUnder D C m L γ δ := Iff.rfl

/-! ### Non-vacuity -/

/-- **The constant learner PAC-learns a class with one concept from no examples** (non-vacuity
of `PACLearns`): if every `C i` is `c₀`, the learner that outputs `c₀` has error `0`, so it learns
at every accuracy `ε ≥ 0` and confidence `δ ≥ 0`. -/
theorem pacLearns_const {C : I → X → Bool} {c₀ : X → Bool} (hC : ∀ i, C i = c₀) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    PACLearns C 0 (fun (_ : Fin 0 → X × Bool) (_ : ρ) => c₀) ε δ := by
  intro D i
  rw [accuracyProb_eq, hC i]
  have h : (fun sr : (Fin 0 → X) × ρ =>
      decide (err D ((fun (_ : Fin 0 → X × Bool) (_ : ρ) => c₀) (label c₀ sr.1) sr.2) c₀ ≤ ε)) =
      fun _ => true := by
    funext sr
    simp only [err_self, hε, decide_true]
  rw [h, FinDist.probTrue_true]
  linarith

/-- **No learner reaches a negative accuracy with confidence `δ < 1`**: the error is
nonnegative, so the accuracy event is empty and its probability `0 < 1 − δ`. So
`PACLearnsUnder` fails at every negative accuracy (a witness outside the sources' range). -/
theorem not_pacLearnsUnder_of_neg (D : FinDist X) {C : I → X → Bool} [Nonempty I] {m : ℕ}
    (L : (Fin m → X × Bool) → ρ → X → Bool) {ε δ : ℝ} (hε : ε < 0) (hδ : δ < 1) :
    ¬ PACLearnsUnder D C m L ε δ := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty I›
  have h1 := h i
  rw [accuracyProb_eq] at h1
  have h0 : (fun sr : (Fin m → X) × ρ => decide (err D (L (label (C i) sr.1) sr.2) (C i) ≤ ε)) =
      fun _ => false := by
    funext sr
    have := err_nonneg D (L (label (C i) sr.1) sr.2) (C i)
    simp only [decide_eq_false_iff_not, not_le]
    linarith
  rw [h0, FinDist.probTrue_eq] at h1
  simp at h1
  linarith

/-- **With no examples, no learner tells two concepts apart** (non-vacuity in the sources'
range): on a one-point domain with the two constant concepts, every learner with `m = 0` fails to
PAC-learn them under the distribution `D`, at every accuracy `ε < 1` and confidence `δ < ½`.

**Proof sketch.** With no examples the labelled sample is the same for both targets, so the
hypothesis depends on the coins only. Its error against the constant `b` is `0` when it outputs
`b` and `1` otherwise, so on every draw it is accurate (error at most `ε < 1`) for at most one of
the two targets. The two accuracy probabilities therefore sum to at most `1`, while learning
would make each at least `1 − δ > ½`. -/
theorem not_pacLearnsUnder_const_pair (D : FinDist Unit)
    (L : (Fin 0 → Unit × Bool) → ρ → Unit → Bool) {ε δ : ℝ} (hε : ε < 1) (hδ : δ < 1 / 2) :
    ¬ PACLearnsUnder D (fun (b : Bool) (_ : Unit) => b) 0 L ε δ := by
  intro h
  -- an accurate hypothesis agrees with the target at the single point
  have hagree : ∀ h' c : Unit → Bool, err D h' c ≤ ε → h' () = c () := by
    intro h' c hle
    by_contra hne
    have hall : (fun x => h' x != c x) = fun _ => true := by
      funext x
      cases x
      simpa using hne
    rw [err_eq, hall, FinDist.probTrue_true] at hle
    linarith
  -- with no examples, the labelled sample does not depend on the target
  have hlab : ∀ (c : Unit → Bool) (s : Fin 0 → Unit), label c s = label (fun _ => true) s :=
    fun _ _ => Subsingleton.elim _ _
  -- on every draw, at most one of the two targets is learned accurately
  have hsum :
      accuracyProb D (fun _ => true) 0 L ε + accuracyProb D (fun _ => false) 0 L ε ≤ 1 := by
    rw [accuracyProb_eq, accuracyProb_eq, FinDist.probTrue_eq_expect,
      FinDist.probTrue_eq_expect, ← FinDist.expect_add]
    calc _ ≤ ((D.iid 0).prod (FinDist.uniform ρ)).expect (fun _ => 1) :=
          FinDist.expect_le_expect _ fun sr => ?_
      _ = 1 := FinDist.expect_const _ _
    dsimp only
    rw [hlab (fun _ => false)]
    generalize L (label (fun _ => true) sr.1) sr.2 = g
    by_cases ht : err D g (fun _ => true) ≤ ε
    · have hf : ¬ err D g (fun _ => false) ≤ ε := fun hf => by
        have := (hagree _ _ ht).symm.trans (hagree _ _ hf)
        simp at this
      simp [ht, hf]
    · by_cases hf : err D g (fun _ => false) ≤ ε <;> simp [ht, hf]
  have h1 : 1 - δ ≤ accuracyProb D (fun _ => true) 0 L ε := h true
  have h0 : 1 - δ ≤ accuracyProb D (fun _ => false) 0 L ε := h false
  linarith

end TCSlib.LearningTheory.PAC

## ===== TCSlib/LearningTheory/PAC/Prediction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.LearningTheory.PAC.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The prediction game, and its bridge to PAC learning

[PS10, §8.1] (Def 179.a of the inventory) asks whether a learner, given labelled examples of a
random concept `C_i`, can predict the label of a fresh point. Under the uniform distribution
(the reading under which the source's Theorem 179.1 works) the game is:
`i ← I`, `m` examples `s ← X^m`, coins `r ← ρ`, a fresh point `x ← X`, all uniform and
independent; the learner wins when `L(s labelled by C_i, r)(x) = C_i(x)`.

**The bridge.** The fresh point is independent of the sample, so for fixed `(i, s, r)` the
probability of a correct prediction is `1 − err_U(h, C_i)` for the hypothesis `h = L(s, r)`.
So the prediction success is `1 − E_{i,s,r}[err_U(L(s, r), C_i)]`
(`predictSuccess_eq_one_sub_expectedErr`), with no collision issue between the fresh point and
the sample. A learner that PAC-learns under the uniform distribution with accuracy `ε ≥ 0` and
confidence `δ` has expected error at most `ε + δ`: split the expectation over the accuracy event,
where the error is at most `ε`, and its complement, of probability at most `δ`, where the error is
at most `1`. Hence its prediction success is at least `1 − ε − δ`, and a learner whose prediction
advantage is at most `γ` does not satisfy `WeakLearnsUnder` under the uniform distribution at an
edge `γ'` and confidence `δ` with `γ + δ < γ' ≤ ½` (`not_weakLearnsUnder_of_predictAdv_le`).

**Use in layer 2.** Layer 2 applies this to each efficient learner, turning [PS10, Thm 179.1]
into a statement at a confidence `δ` below the gap `γ' − γ`. A weak learner of
[KV94, §4.1, p. 74] need only succeed with probability `1/q(n, size(c))`, that is, at the
confidence `δ = 1 − 1/q(n, size(c))`. To reach a small `δ` it must first be amplified
([KV94, §4.2, pp. 76–77]), which gives a different learner; layer 2 must account for that
learner's sample count, running time and edge before applying the bridge.
Information-theoretically the class is learnable; the hardness is computational.

**Source notes.** [PS10] leaves the sample distribution and "a new sample" implicit; uniform
and independent is the reading (design note S3d). "Better than `½ + ε`" is the advantage
`|Pr[correct] − ½|`.

## Main definitions

* `PAC.trialDist X I ρ m`: the joint law of the concept index, the examples and the coins.
* `PAC.predictSuccess C m L`, `PAC.predictAdv C m L`: the success probability of the prediction
  game, and its advantage over `½`.
* `PAC.expectedErr C m L`: the expected uniform error of the learner's hypothesis.

## Main results

* `PAC.predictSuccess_eq_one_sub_expectedErr`: **the bridge**, success `= 1 − E[err]`.
* `PAC.expectedErr_le_of_pacLearnsUnder`, `PAC.one_sub_sub_le_predictSuccess`: PAC learning
  under the uniform distribution with accuracy `ε ≥ 0` gives expected error at most `ε + δ` and
  success at least `1 − ε − δ`.
* `PAC.sub_le_predictAdv_of_weakLearnsUnder`, `PAC.not_weakLearnsUnder_of_predictAdv_le`: the
  weak-learning condition at edge `γ' ≤ ½` and confidence `δ` gives advantage at least `γ' − δ`;
  so advantage at most `γ` rules it out when `γ + δ < γ' ≤ ½`.
* `PAC.predictSuccess_coin`: the learner that outputs its coin succeeds with probability exactly
  `½` (non-vacuity).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1 (book p. 179).
* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994, §1.2, §4.1 (p. 74) and §4.2 (pp. 76–77).
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, ch. 3.
-/

namespace TCSlib.LearningTheory.PAC

open TCSlib.InformationTheory Finset

variable {X I ρ : Type*} [Fintype X] [Nonempty X] [Fintype I] [Nonempty I] [Fintype ρ]
  [Nonempty ρ]

/-! ### The game -/

variable (X I ρ) in
/-- The joint law of a trial of the prediction game: a uniform concept index, `m` uniform
independent examples and uniform coins. -/
noncomputable def trialDist (m : ℕ) : FinDist (I × ((Fin m → X) × ρ)) :=
  (FinDist.uniform I).prod (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ))

/-- The trial law is the product of the uniform index, the `m` uniform examples and the uniform
coins. -/
theorem trialDist_eq (m : ℕ) :
    trialDist X I ρ m =
      (FinDist.uniform I).prod (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ)) := rfl

/-- **The prediction game** [PS10, §8.1]: the probability that the learner `L`, given `m`
uniform examples labelled by a uniform concept `C_i` and uniform coins, predicts the label of a
fresh uniform point. [PS10] leaves the sample law and "a new sample" implicit. Here both are
uniform and independent, so the fresh point may coincide with an example. -/
noncomputable def predictSuccess (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  ((trialDist X I ρ m).prod (FinDist.uniform X)).probTrue
    fun w => L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2

/-- The success probability is the probability, over a trial `(i, (s, r)) ← trialDist` and an
independent uniform point `x`, of the event `L(s labelled by C_i, r)(x) = C_i(x)`. -/
theorem predictSuccess_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictSuccess C m L = ((trialDist X I ρ m).prod (FinDist.uniform X)).probTrue
      (fun w => L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2) := rfl

/-- The **prediction advantage** `|Pr[correct] − ½|` [PS10, §8.1, proof of Thm 179.1]: "better
than `½ + ε`", read two-sidedly. An upper bound on it bounds the one-sided success. -/
noncomputable def predictAdv (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  |predictSuccess C m L - 1 / 2|

/-- The prediction advantage is `|predictSuccess − ½|`. -/
theorem predictAdv_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictAdv C m L = |predictSuccess C m L - 1 / 2| := rfl

/-- The **expected error** `E_{i,s,r}[err_U(L(s labelled by C_i, r), C_i)]` of the learner's
hypothesis under the uniform distribution. -/
noncomputable def expectedErr (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  (trialDist X I ρ m).expect
    fun t => err (FinDist.uniform X) (L (label (C t.1) t.2.1) t.2.2) (C t.1)

/-- The expected error is the expectation, over a trial `(i, (s, r)) ← trialDist`, of the
uniform error `err_U(L(s labelled by C_i, r), C_i)`. -/
theorem expectedErr_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    expectedErr C m L = (trialDist X I ρ m).expect
      (fun t => err (FinDist.uniform X) (L (label (C t.1) t.2.1) t.2.2) (C t.1)) := rfl

/-! ### The bridge -/

/-- **The bridge: prediction success is one minus the expected error.**

**Proof sketch.** Split the fresh point off the trial (`expect_prod`). For a fixed trial with
hypothesis `h`, the correct-prediction indicator is one minus the disagreement indicator, so its
expectation over the uniform fresh point is `1 − err_U(h, C_i)` (`expect_one_sub`); then take the
expectation over the trial. -/
theorem predictSuccess_eq_one_sub_expectedErr (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictSuccess C m L = 1 - expectedErr C m L := by
  rw [predictSuccess_eq, FinDist.probTrue_eq_expect, FinDist.expect_prod, expectedErr_eq,
    ← FinDist.expect_one_sub]
  congr 1
  funext t
  dsimp only
  rw [err_eq, FinDist.probTrue_eq_expect, ← FinDist.expect_one_sub]
  congr 1
  funext x
  cases L (label (C t.1) t.2.1) t.2.2 x <;> cases C t.1 x <;> simp

/-- **PAC learning under the uniform distribution bounds the expected error** by `ε + δ`
(for `ε ≥ 0`).

**Proof sketch.** For each concept `C_i`, the error is at most `1`, and at most `ε` except with
probability at most `δ` (the hypothesis `PACLearnsUnder`), so its expectation over the examples
and coins is at most `ε + δ` (`expect_le_add_of_le_one`, `probTrue_not`); average over `i`. -/
theorem expectedErr_le_of_pacLearnsUnder {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {ε δ : ℝ}
    (h : PACLearnsUnder (FinDist.uniform X) C m L ε δ) (hε : 0 ≤ ε) :
    expectedErr C m L ≤ ε + δ := by
  rw [expectedErr_eq, trialDist_eq, FinDist.expect_prod]
  calc _ ≤ (FinDist.uniform I).expect (fun _ => ε + δ) := FinDist.expect_le_expect _ fun i => ?_
    _ = ε + δ := FinDist.expect_const _ _
  dsimp only
  have h1 := FinDist.expect_le_add_of_le_one (((FinDist.uniform X).iid m).prod
    (FinDist.uniform ρ)) (f := fun b => err (FinDist.uniform X) (L (label (C i) b.1) b.2) (C i))
    (fun b => err_le_one _ _ _) hε
  have h2 := h i
  rw [accuracyProb_eq] at h2
  have h3 := FinDist.probTrue_not (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ))
    (fun b => decide (err (FinDist.uniform X) (L (label (C i) b.1) b.2) (C i) ≤ ε))
  dsimp only at h1 h2 h3
  linarith

/-- **PAC learning under the uniform distribution gives prediction success at least
`1 − ε − δ`** (for `ε ≥ 0`): the bridge and `expectedErr_le_of_pacLearnsUnder`. -/
theorem one_sub_sub_le_predictSuccess {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {ε δ : ℝ}
    (h : PACLearnsUnder (FinDist.uniform X) C m L ε δ) (hε : 0 ≤ ε) :
    1 - ε - δ ≤ predictSuccess C m L := by
  rw [predictSuccess_eq_one_sub_expectedErr]
  linarith [expectedErr_le_of_pacLearnsUnder h hε]

/-- **Weak learning under the uniform distribution gives prediction advantage at least
`γ − δ`** (for `γ ≤ ½`): success is at least `1 − (½ − γ) − δ = ½ + γ − δ`. -/
theorem sub_le_predictAdv_of_weakLearnsUnder {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {γ δ : ℝ}
    (h : WeakLearnsUnder (FinDist.uniform X) C m L γ δ) (hγ : γ ≤ 1 / 2) :
    γ - δ ≤ predictAdv C m L := by
  have hs := one_sub_sub_le_predictSuccess ((weakLearnsUnder_iff _ _ _ _ _ _).1 h)
    (by linarith)
  rw [predictAdv_eq]
  exact le_trans (by linarith) (le_abs_self _)

/-- **Small prediction advantage rules out the weak-learning condition below the gap**: if the
learner's prediction advantage is at most `γ`, it does not satisfy `WeakLearnsUnder` under the
uniform distribution at any edge `γ' ≤ ½` and confidence `δ` with `γ + δ < γ'`. The confidence
must be below the gap: at a constant confidence such as `δ = ½`, a learner with zero prediction
advantage can satisfy `WeakLearnsUnder`.

A weak learner of [KV94, §4.1, p. 74] need only succeed with probability `1/q(n, size(c))`, that
is, at the confidence `δ = 1 − 1/q(n, size(c))`, which in general is not below the gap. Starting
from that definition, applying this lemma at a small `δ` needs confidence amplification
([KV94, §4.2, pp. 76–77]), which gives a different learner, with its own sample count, running
time and edge. It is that learner's certified edge `γ'`, sample count `m` and prediction
advantage `γ` that enter here. -/
theorem not_weakLearnsUnder_of_predictAdv_le {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {γ γ' δ : ℝ} (hadv : predictAdv C m L ≤ γ)
    (hlt : γ + δ < γ') (hγ' : γ' ≤ 1 / 2) :
    ¬ WeakLearnsUnder (FinDist.uniform X) C m L γ' δ := fun h => by
  have := sub_le_predictAdv_of_weakLearnsUnder h hγ'
  linarith

/-! ### Non-vacuity -/

omit [Nonempty X] [Fintype I] [Nonempty I] in
/-- Against any target, the two constant hypotheses have errors summing to one, so a fair coin
between them has expected error `½`. -/
theorem expect_err_coin (D : FinDist X) (c : X → Bool) :
    (FinDist.uniform Bool).expect (fun r => err D (fun _ => r) c) = 1 / 2 := by
  have hnot : err D (fun _ => true) c = 1 - err D (fun _ => false) c := by
    simpa using err_not D (fun _ => false) c
  rw [FinDist.expect_eq, Fintype.sum_bool]
  simp only [FinDist.uniform_apply, Fintype.card_bool]
  rw [hnot]
  push_cast
  ring

/-- **The coin-flipping learner predicts with probability exactly `½`** (non-vacuity of the
game): the learner that ignores its examples and outputs its coin.

**Proof sketch.** By the bridge, the success is one minus the expected error; for every concept
and every sample, the error averaged over the coin is `½` (`expect_err_coin`). -/
theorem predictSuccess_coin (C : I → X → Bool) (m : ℕ) :
    predictSuccess C m (fun (_ : Fin m → X × Bool) (r : Bool) (_ : X) => r) = 1 / 2 := by
  rw [predictSuccess_eq_one_sub_expectedErr, expectedErr_eq, trialDist_eq, FinDist.expect_prod]
  dsimp only
  have hin : ∀ i, (((FinDist.uniform X).iid m).prod (FinDist.uniform Bool)).expect
      (fun b => err (FinDist.uniform X) (fun _ => b.2) (C i)) = 1 / 2 := by
    intro i
    rw [FinDist.expect_prod]
    dsimp only
    simp only [expect_err_coin]
    exact FinDist.expect_const _ _
  simp only [hin, FinDist.expect_const]
  norm_num

end TCSlib.LearningTheory.PAC

## ===== TCSlib/LearningTheory/PAC.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.LearningTheory.PAC.Defs
import TCSlib.LearningTheory.PAC.Prediction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PAC learning

Probably approximately correct learning over a finite domain, information-theoretic (learners
are arbitrary functions with finite coins), and the prediction game of [PS10, §8.1] with its
bridge to PAC learning.

## Contents

* `TCSlib.LearningTheory.PAC.Defs`: error, labelled samples, PAC, weak and fixed-distribution
  learning, for a given learner at fixed parameters.
* `TCSlib.LearningTheory.PAC.Prediction`: the prediction game; success `= 1 − E[err]`, so
  a small prediction advantage rules out the weak-learning condition under the uniform
  distribution, for that learner, at a confidence below the gap (for a weak learner of
  [KV94, §4.1], only after confidence amplification, [KV94, §4.2], which changes the learner).

## References

* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994.
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

## ===== design/S3d-pac-learning.md =====

# S3d design note: PAC learning in `TCSlib/LearningTheory` (decision D-5)

Status: **draft, 2026-11-04.** D-5 (user): Def 179.a and Thm 179.1 are built on a PAC framework in
`TCSlib/LearningTheory`, not on a crypto-style one-off game. No PAC development exists in the
pinned Mathlib or on any branch (`main`, ch. 2–4, ch. 3–4, Garg), so this is new. `main`'s
`LearningTheory` has online learning (`MistakeBounds`, `Hedge`), Johnson–Lindenstrauss and
minimax, by other authors; their files are not touched.

## What [PS10] §8.1 says (PDF p. 191, book p. 179)

- **The learning question** (Def 179.a, informal):
  - a space `S ⊆ {0,1}^n` and concepts `C_i ⊆ S` for `i ∈ I`;
  - for a random `i`, given samples `(x_j, b_j)` with `b_j = [x_j ∈ C_i]`, decide whether a new
    `x` is in `C_i`.
- **Thm 179.1:** there is a p.p.t.-decidable concept class that cannot be learned. The proof
  sketch is: `S = {0,1}^n`, `I = {0,1}^n`, `C_i = {x : f_i(x)|₁ = 1}` for a PRF `{f_i}`; no
  non-uniform PPT predicts membership of a new sample better than `½ + ε`.
- **Left implicit** (recorded as deviations when stated):
  - the sample distribution: uniform on `S` is the reading under which the sketch works;
  - "a new sample": uniform and independent;
  - "better than `½ + ε`": `ε` non-negligible.

## Two layers

### Layer 1: information-theoretic PAC (`TCSlib/LearningTheory/PAC/`, no machines)

Second source: [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning
Theory*, MIT Press 1994, §1.2 (PAC), §4 (weak learning), and [SSBD14] S. Shalev-Shwartz,
S. Ben-David, *Understanding Machine Learning*, ch. 3. The definitions:

- **Basic objects:** a finite domain `X`; a concept `c : X → Bool`; a concept class, indexed as
  `C : I → X → Bool` (which matches [PS10]'s `{C_i}`).
- **Distributions:** `D : FinDist X`, `main`'s `InformationTheory.FinDist`, reused, so samples,
  products and `statDist` are shared with #183.
- **Error:** `err D h c := ∑_{x : h x ≠ c x} D x`.
- **Samples:** a labelled sample of size `m` is `Fin m → X × Bool`, drawn as `D^m`, labelled by
  `c`.
- **Learners:** a (randomized) learner is `L : (Fin m → X × Bool) → ρ → (X → Bool)`, with finite
  coins `ρ`.
- **PAC learning:** `PACLearns C m L ε δ :=` for every `i` and every `D`, with probability
  `≥ 1 − δ` over the sample and the coins, `err D (L S r) (C i) ≤ ε`. Variants:
  - weak learning: `ε = ½ − γ` [KV94, §4];
  - learning under a fixed distribution: `D` fixed to uniform, the case [PS10] needs.
- **The prediction game (Def 179.a):** sample `i`, `m` examples and a fresh `x`, all uniform;
  the learner predicts `C i x`.
- **The bridge (proved here):** the prediction success equals `1 − E_{i,S,r}[err_U(L S r, C i)]`.
  The fresh point is independent of the sample, so no fresh-point collision issue arises. Hence
  a learner with prediction advantage `≤ γ` does not satisfy `WeakLearnsUnder U C m L γ' δ`
  whenever `γ + δ < γ' ≤ ½`: split the expected error over the accuracy event (error at most
  `½ − γ'`) and its complement (probability at most `δ`, error at most 1). Starting from
  [KV94, §4.1, p. 74]'s weak learner, which succeeds only with probability `1/q`, a small `δ`
  needs confidence amplification [KV94, §4.2, pp. 76–77]; layer 2 applies the bridge to the
  amplified learner, with its own sample count, running time and edge (gate 05, round 2, R2-1
  and R2-2).

### Layer 2: efficient learning and Thm 179.1 (prong D, `TCSlib/Cryptography/Randomness/`)

- **Efficient learner.** A learner is a NUPPT, run through the S2 framework:
  - the **example oracle** `EX(C i, U)` is a handler that samples `x ← U` and answers
    `(x, C i x)`;
  - the learner queries it polynomially often, then receives the challenge `x` and outputs a bit;
  - asymptotically, the learner is decoded by `NUPPT.toComp`.

  This is the PAC model's own example oracle, so the efficient prediction game is an S2 game,
  and its concrete probability is layer 1's prediction game (a bridge).
- **Thm 179.1, stated:** for a PRF `F` (Frederick's `PRF`), the class `C_n(k) = {x : F n k x 0 =
  true}`:
  - (a) is p.p.t.-decidable given `k` (from `PRF.easy`);
  - (b) for every NUPPT learner and polynomial sample count, the prediction advantage
    `|Pr[correct] − ½|` is negligible;
  - (c) as a corollary through layer 1's bridge, no efficient learner weakly PAC-learns `C` under
    the uniform distribution with a noticeable `γ`.
- **Proof route (for the S4 sketch):**
  1. replace the PRF by a random function (S2 §5's oracle substitution: the reduction answers the
     example oracle with PRF queries at uniform points, and the challenge with one more query);
  2. against a random function, the fresh `x`'s label is a uniform bit independent of the view
     unless `x` was sampled, with probability `≤ m · 2^{-n}`;
  3. so the advantage is at most `negl + m · 2^{-n}`.

## Placement and landing

- **Layer 1** needs nothing from ch. 2–4. **Ruled (R-3):** it lands on `main` by its own PR, like
  P0 (D-1), with its own gate. That depends on `main`'s `FinDist` only. Since all of S2 stays on the
  ch. 2–4 branch (ruled 2026-11-04), layer 1 does not refer to S2; the bridge from its prediction
  game to S2's example-oracle game is part of layer 2.
- **Layer 2** needs `NUPPT`, `PRF` and S2, so it lives on the ch. 2–4 branch in prong D.
- **Size estimate:** layer 1 about 400–700 lines; layer 2 about 300–600, beyond S2.

## Decision for the user (ruled 2026-11-04: R-3, its own PR to `main`, written after S2 settles)

- **R-3:** where the information-theoretic PAC layer lands: on `main` by its own PR, now or after
  S2 (recommended, as for P0), or with prong D on the ch. 2–4 branch.

## ===== resolutions-r1.md =====

# Gate 05 (PAC layer, #194): round 1 resolutions

- **Round 1:** findings `findings/gate05-pac-findings.md`, verbatim, SHA-256
  `06adae4b5571db4b84c221eeb838f50e9ba5b21dbc89e340529907ed54ca2f16`; head
  `44d27f39c233849a3a30a117bf15434610e485e9`. Counts: **0 blockers, 1 major (F1), 8 minors, 7 notes.**
- **Review:** `review/gate05-review.md`: 11 true, 5 partly true, none false; F5 moved from minor to
  note.
- **Rulings (user, 2026-11-05):** G5-1, remove `PACLearnable` and `pacLearnable_iff` and rewrite the
  deviation as a statement about single learners; G5-2, move `FinDist.probTrue` into `FinDist.lean`
  later, in a small PR to `main`.
- **Repair:** one commit on #194's branch, `6b781240bc438a103291c74b2ffefaa910f1a70d` (full diff
  `evidence-r2/repair.diff.txt`). Elaboration of the four changed modules and lint: maintainer's
  re-check (`evidence-r2/checks.log`). Axioms (worker's run): 37 of the 38 theorems print within
  `propext`, `Classical.choice` and `Quot.sound`; `PAC.label_apply` uses none; no `sorryAx`.

| Finding | Severity | Resolution |
|---|---|---|
| F1 | major | **Fixed** (G5-1). `PACLearnable` and `pacLearnable_iff` removed. The "Fixed parameters" deviation is replaced by a single-learner statement ([KV94, §1.2.1]). `PACLearns`'s docstring ("a PAC learner at fixed parameters"), the `PAC.lean` contents line and `Prediction.lean:27–28` rewritten. Nothing says that the negation of a fixed-parameter predicate is non-learnability, and [SSBD14, Def 3.1] is no longer said to require a polynomial sample size. |
| F2 | minor | **Fixed.** Parameter ranges and degenerate cases stated for `PACLearnsUnder`, `PACLearns`, `WeakLearnsUnder` and `WeakLearns`. `not_pacLearnsUnder_of_neg` reworded ("a witness outside the sources' range"). **New:** an in-range witness `not_pacLearnsUnder_const_pair` (no examples, the two constant concepts on a one-point domain, `ε < 1`, `δ < ½`). An "Unrestricted parameters" deviation bullet is added. The review's text "`ε < 0` or `δ < 0`" was corrected to "either `δ < 0`, or `ε < 0` and `δ < 1`". |
| F3 | minor | **Fixed.** An "Improper hypotheses" deviation bullet. |
| F4 | minor | **Fixed.** A "Coins" deviation bullet; the coins are not generalized to `FinDist ρ` (the review's advice). |
| F5 | note (was minor) | **Fixed** (documentation): `not_weakLearnsUnder_of_predictAdv_le` says the confidence must be below the gap. |
| F6 | minor | **Fixed.** `PACLearnsUnder` tagged as the fixed-distribution variant of [KV94, §1.2.1] / [SSBD14, Def 3.1]; `WeakLearns(Under)` cite [KV94, §4.1] and state the fixed real edge and confidence. |
| F7 | minor | **Fixed.** The [PS10] reading is on `predictSuccess`; `predictAdv` has its tag and the two-sided reading. |
| F8 | minor | **Fixed.** The four `_iff` lemmas, `accuracyProb_eq`, `predictSuccess_eq` and `expectedErr_eq` state their formulas in their docstrings. |
| F9 | minor | **Recorded** (G5-2): `probTrue` moves into `FinDist.lean` in a follow-up PR to `main` (queued). |
| F10 | note | No change (observation). |
| F11 | note | **Fixed.** `Samples.lean` says "values at most `1`". |
| F12 | note | **Fixed.** `ε ≥ 0` and `γ' ≤ ½` stated in `Prediction.lean`'s module docstring; the optional sharper lemmas are not added. |
| F13 | note | No change (the marginal lemma for `iid` is not needed by any statement). |
| F14 | note | **Partly fixed.** The unused [Vad12] reference is dropped; the [SSBD14, §2.3.1] location stays until checked against the book. |
| F15 | note | Recorded: the pack's attestations are refreshed in this round (`evidence-r2/`). |
| F16 | note | **Resolved** by the review from the source text (p. 179). |
