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

