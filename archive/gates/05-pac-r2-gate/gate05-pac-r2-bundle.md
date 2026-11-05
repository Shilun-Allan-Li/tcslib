## ===== briefs/pass-shelat-ch5-8/gates/05-pac/pack-r2.md =====

# Gate 05 (Pass–shelat ch. 5–8, S3d layer 1), round 2: external closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194)
into `main`, at its head `6b781240bc438a103291c74b2ffefaa910f1a70d`.
- **Round 1** audited `44d27f39c233849a3a30a117bf15434610e485e9` and found **0 blockers, 1 major,
  8 minors and 7 notes** (`gate05-pac-findings.md`, in the bundle, verbatim).
- **The repair:** one commit, `6b781240`. Its full diff is `evidence-r2/repair.diff.txt`; each
  finding's resolution is in `resolutions-r1.md` (both in the bundle).
- **The deliverable:** **`gate05-pac-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] (PDF; book page = PDF page − 12; the item is on
book p. 179).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each of the 16 findings say whether the resolution
   is adequate: **fixed** (the defect is gone, and the fix introduces no new one), **recorded**
   (accepted as declared or scheduled, and the record is accurate), or **not resolved** (say why).
2. **It audits the changed surface afresh:** the rewritten deviations and docstrings, and the new
   theorem `not_pacLearnsUnder_const_pair` (restate it in your own words, and say whether its
   statement is what its docstring claims). Look for regressions: anything round 1 accepted that
   the repair broke. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Round 1 findings, resolutions, repair diff | `gate05-pac-findings.md`, `resolutions-r1.md`, `evidence-r2/repair.diff.txt` |
| Changed Lean, at `6b781240` | `TCSlib/InformationTheory/Samples.lean`, `TCSlib/LearningTheory/PAC/{Defs, Prediction}.lean`, `TCSlib/LearningTheory/PAC.lean` |
| Context | `policy.md`; `design/S3d-pac-learning.md` §"Layer 1" |

## Attestations (maintainer execution claims; `evidence-r2/`)

- **Elaboration:** the four changed modules, rechecked in import order at `6b781240`: all pass, with
  0 errors and 0 warnings (`checks.log`).
- **`sorry`:** none.
- **Axioms** (worker's run, reported): 37 of 38 theorems within `propext`, `Classical.choice` and
  `Quot.sound`; `PAC.label_apply` uses none.
- **Lint:** 0 findings in each of the four files.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 finding: `F<n>: fixed / recorded / not resolved — <reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major** (fixable
but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge case,
naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== gate05-pac-findings.md =====

# Gate 05 (Pass–shelat ch. 5–8, S3d layer 1, PAC learning): external audit findings

- **Audited:** [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194) at head
  `44d27f39c233849a3a30a117bf15434610e485e9`, base `main` at `7d36bbc27dfabd4988ee1702bc342049a1f3e006`.
- **Scope:** as in the pack. Trusted surface of `Samples.lean`, `PAC/Defs.lean`, `PAC/Prediction.lean`
  (14 definitions, 38 theorems), the three facades, and the docstring citations. Tactic scripts were not reviewed.
- **Auditor:** Claude (AI external auditor), 2026-11-05.

## Verdict

**The gate does not close as staged: 0 blockers, 1 major, 8 minors, 7 notes.**

Every one of the 38 theorem statements is true and says what its docstring says. No Lean statement is wrong, so
there is no blocker. The one major (F1) is in the trusted prose. The declared deviation says that `PACLearnable`
is "weaker, so impossibility results stated with it are stronger". At a fixed sample size `m` that claim is false.
Over a finite domain, the strong reading (no `m` works) can never hold for `ε, δ ∈ (0,1)`, and that includes the
PRF class of [PS10, Thm 179.1]. F1 needs only a docstring rewrite. After it, the gate can close. Of the minors, I
recommend F5 (how layer 2 must quantify the confidence `δ` in Thm 179.1(c)) and F2/F4 (undeclared parameter
ranges and coin model) before layer 2 is briefed.

## 0. Sources, and what I could and could not check

- **Bundle:** read in full.
  - I cloned the public repository and checked that all eight files in the bundle (the six of the diff plus
    `FinDist.lean` and `StatisticalDistance.lean`) are identical to their versions at the PR head.
  - The PR diff against the base is exactly six files (646 insertions).
  - The base equals the current `main` head.
- **[PS10] PDF: not available to me.**
  - Only the bundle reached the session. The PDF named in the request was not attached.
  - `cs.cornell.edu`, which hosts the notes, is blocked by this session's network policy.
  - A web search hit on the notes' table of contents confirms the location: §8.1 "A Negative Result for
    Learning", p. 179.
  - My [PS10] fidelity checks rest on the design note's transcription of the learning question and of the
    Thm 179.1 sketch, plus my own knowledge of the notes. **A human should spot-check p. 179's wording before
    closing (F16).**
- **[KV94], [SSBD14]:** from my knowledge, as the pack allows. Section numbers I am not certain of are marked
  "(from memory)".
- **Not done:** I did not run Lean (no elaboration, axiom or lint rerun). Section 6 lists which attestations I
  cross-checked mechanically.
- **Exact checks:** I modelled the definitions literally on small finite instances, in exact rational
  arithmetic and in exact arithmetic in ℚ(√3). This covers the bridge (300 random instances), the
  expected-error bound, and the counterexamples A4 and A5 below. Appendix B has the derivations.

## 1. Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F1 | **major** | `PAC/Defs.lean` · module docstring ("Deviations … Fixed parameters"); `PACLearnable`, `PACLearns` docstrings | The declared deviation says `PACLearnable C m ε δ` is "weaker, so impossibility results stated with it are stronger". **At a fixed `m` this is false.** The source notion gives `PACLearnable` only for `m ≥ m_H(ε, δ)`, so `¬ PACLearnable C m ε δ` is a sample-size lower bound, not non-learnability. Over a finite `X`, every class satisfies `PACLearnable C m ε δ` for all `ε, δ ∈ (0,1)` once `m` is large. So the strong reading (no `m` works) is never true, and no impossibility result of the intended kind can be stated with this predicate. The note also misdescribes [SSBD14, Def 3.1] as requiring a sample size polynomial in `1/ε, 1/δ`: there `m_H` is an arbitrary function, and polynomial bounds come from [KV94]'s efficiency requirement. The deviation appears only in the module docstring. `PACLearnable`'s own docstring, which is what blind restatements and the blueprint/dataset are compared against, does not say that it is not the textbook notion. | **A2:** take `X = Bool` and `C = id : (Bool → Bool) → Bool → Bool`, i.e. all 4 concepts. Then `¬ PACLearnable C 0 (1/4) (1/2)`: under uniform `D` the learner's hypothesis cannot depend on the target, so the four targets' accuracies sum to 1. Yet ERM gives `PACLearnable C 9 (1/4) (1/2)` (`m ≥ ln(4/δ)/ε`, [SSBD14, Cor. 3.2], from memory), and `C` is PAC-learnable in the sources' sense. **A3:** the PRF-shaped class `C_k(x) = f_k(x)₁`, `k ∈ {0,1}ⁿ`, is `PACLearnable` at `m = ⌈(n ln 2 + ln(1/δ))/ε⌉`, which is polynomial: ERM over `2ⁿ` keys. So a layer-2 statement of Thm 179.1(c) as `¬ PACLearnable …` would be false. The hardness is computational and can only be stated per learner, as `Prediction.lean` does. | Rewrite the bullet, and repeat it in `PACLearnable`'s docstring. Suggested text: *"This is not the learnability of [SSBD14, Def 3.1] / [KV94, §1.2]. Those ask for one algorithm for all `ε, δ ∈ (0,1)`, with a sample function `m_H(ε, δ)` (and, in [KV94], polynomial running time). A source-learnable class satisfies `PACLearnable C m ε δ` at `m = m_H(ε, δ)`, and so at every larger `m`, because extra examples can be ignored. So `¬ PACLearnable C m ε δ` says `m_H(ε, δ) > m`. Over a finite `X` every class is `PACLearnable` for large `m` (ERM). Computational hardness such as [PS10, Thm 179.1] is therefore stated per learner, not with this predicate."* Optionally rename it `PACLearnableAt` and add the monotonicity-in-`m` lemma that the sentence relies on. |
| F2 | minor | `PAC/Defs.lean` · `PACLearnsUnder`, `PACLearns`, `WeakLearns(Under)`, `PACLearnable`; docstring of `not_pacLearnsUnder_of_neg` | **Degenerate parameter ranges are accepted and not declared.** The sources take `ε, δ ∈ (0,1)` ([SSBD14]) or `(0,½)` ([KV94], from memory). The predicates hold for **every** learner, at every parameter value, in these cases: `ε ≥ 1` (error is at most 1), `δ ≥ 1` (since `1 − δ ≤ 0`), and `I` empty, as in the sources. For weak learning, `γ ≤ −½` is trivial, and `γ ≤ 0` is not weak learning in any sense. The PR's only falsity witness, `not_pacLearnsUnder_of_neg`, uses `ε < 0`, which is outside every source's range. Its docstring nevertheless concludes "`PACLearns` is therefore not trivially satisfied". No in-range negative instance is proved. | **A1** (table in §4). The in-range falsity of A2 shows the predicate is meaningful, but the PR does not prove it. | State the unrestricted ranges and the trivial cases in the docstrings of `PACLearnsUnder`/`PACLearns`/`WeakLearnsUnder`. Reword `not_pacLearnsUnder_of_neg`'s conclusion to "is not satisfied at negative accuracy". Add an in-range non-vacuity theorem: for `X = Bool`, the full class, `m = 0`, uniform `D`, `ε < ½`, `δ < ¾`, no learner `PACLearnsUnder` (A2). |
| F3 | minor | `PAC/Defs.lean` · `PACLearns`, module "Deviations" | **Improper (representation-independent) learning is not declared.** The learner may output any `X → Bool`. [KV94, §1.2.1, Def 1] (from memory) requires `h ∈ C`, and representation classes `H` come later ("PAC learnable using H"). [SSBD14, Def 3.1] does not require `h ∈ H`. This is the right choice for [PS10] and for hardness, because it is the strongest form of an impossibility. But it is a deviation from one of the two cited definitions and must be stated. | Compare the docstrings of `PACLearns` and the module header with KV94 Def 1's "outputs a hypothesis concept h ∈ C". | Add a bullet: *"Hypotheses are arbitrary `X → Bool` (representation-independent, improper learning). [KV94, Def 1] requires `h ∈ C`; impossibility results are stronger without the restriction."* |
| F4 | minor | `PAC/Defs.lean` · `accuracyProb`, `PACLearnable` (coin model) | **The coins are uniform on a finite type, and this is not declared.** That covers every randomized algorithm with bounded running time (`ρ = {0,1}^T`). It is strictly narrower than an arbitrary randomized learner when the distribution and parameters are fixed: a mixing probability that a finite uniform coin space cannot realize may be required exactly. So `¬ ∃ ρ L, PACLearnsUnder D C m L ε δ` does not rule out randomized learners in general at boundary parameters. I did not construct a distribution-free (`PACLearns`) instance. | **A5:** `X = {a, b}`, `D(a) = 1/√3`, concepts `(0,0), (0,1), (1,1)`, `m = 1`, `ε = 1/10`, `δ = 1/3`. A learner that puts mass `1/√3` on `(0,1)` after seeing `(a, 0)` reaches accuracy exactly `2/3` on all three concepts. Every learner that reaches `2/3` must use exactly this irrational mixing, so no finite uniform `ρ` works. (Exact check in ℚ(√3); the best uniform space with at most 60 points reaches ≈ 0.6663.) | Either declare it (*"exact for fair-coin algorithms with bounded running time; at a fixed `D` and exact threshold parameters, narrower than arbitrary randomized learners"*), or generalize the coins to `μ : FinDist ρ` in `accuracyProb`, of which uniform is a special case. The second is advisable if a fixed-distribution learnability predicate is ever introduced. |
| F5 | minor | `PAC/Prediction.lean` · `not_weakLearnsUnder_of_predictAdv_le` (and design note S3d, layer 1) | The statement is correct and matches its docstring. But **it refutes weak learning only at a confidence `δ < γ' − γ`**. For constant confidence it says nothing, and that cannot be improved: a learner with zero prediction advantage can satisfy `WeakLearnsUnder` at `δ = ½` for every `γ' ≤ ½`. So layer 2's Thm 179.1(c) is a consequence of this bridge only if it is stated at a small `δ`. The design note also says "cannot weakly PAC-learn with **any** `γ' > γ`", which is stale (the code correctly has `γ' > γ + δ`), and it calls the step "Markov on the error" (see F11). | **A4:** `X = {a}`, `C b = const b` for `b : Bool`, `m = 1`. The learner reads the label and flips it on coin `true`. Exactly: `predictSuccess = ½` and `predictAdv = 0`, while the minimum accuracy at `ε = ½ − γ'` is `½ = 1 − δ` for `γ' ∈ {½, 1/10}`. | Add to the docstring: *"The confidence must be below the gap. At constant confidence (e.g. `δ = ½`) a learner with zero advantage can weakly learn. To refute weak learning in the sense of [KV94, §4.1], where every `δ` must be achievable in time polynomial in `1/δ`, apply this at `δ = (γ' − γ)/2`. For a fixed constant `δ`, first boost the confidence [KV94, §4.2], which changes `m`."* Fix the design note. When layer 2's (c) is statement-gated, check that its `δ` is quantified in one of these two ways. |
| F6 | minor | `PAC/Defs.lean` · `PACLearnsUnder`, `WeakLearnsUnder`, `WeakLearns` | **Attribution and deviation gaps in the variants.** `PACLearnsUnder` has no `[Tag, location]`, and fixed-distribution learning is not the definition of [KV94, §1.2]. `WeakLearnsUnder` cites "[KV94, §4]", but KV94's weak learning differs in three ways (from memory): it is distribution-free; its advantage is `γ = 1/p(n, size(c)) > 0`, where here `γ` is any real of any sign; and `δ` is an input that must work for every value, where here it is fixed. "§4" is a chapter; weak learning is defined in §4.1 (from memory). All of these restrictions make the predicate easier to satisfy, so impossibility results are stronger. That is the right direction, but it is not stated on the declarations. | Compare the docstrings with KV94 §4.1. | Tag `PACLearnsUnder` as *"the fixed-distribution variant of [KV94, §1.2] / [SSBD14, Def 3.1], the case [PS10, §8.1] needs; weaker than distribution-free learning"*. On `WeakLearns(Under)`, state the fixed real `γ` (and that `γ ≤ 0` is not weak learning) and the fixed `δ`, and cite `[KV94, §4.1]`. |
| F7 | minor | `PAC/Prediction.lean` · `predictSuccess`, `predictAdv` | **The readings of [PS10] are declared only in the module docstring ("Source notes"), not on the declarations.** Policy §2 attaches deviations to the declaration docstring, which is what the dataset extracts. The readings are: uniform examples; a fresh point that is uniform and independent, and so may coincide with an example; a uniform index; and the two-sided advantage for "better than ½ + ε". | Compare `predictSuccess`'s docstring with the "Source notes" paragraph. | Move one sentence onto each declaration. For `predictSuccess`: *"[PS10] leaves the sample law and 'a new sample' implicit; here both are uniform and independent, so the fresh point may coincide with an example."* For `predictAdv`: *"'better than ½ + ε' read two-sidedly; the one-sided bound follows."* |
| F8 | minor | `PAC/Defs.lean` · `pacLearnsUnder_iff`, `pacLearns_iff`, `weakLearnsUnder_iff`, `weakLearns_iff`, `pacLearnable_iff` | **The docstrings are bare labels ("`PACLearnsUnder` unfolded.").** Policy §1 says "each docstring states its formula", and §2 says "a bare label … is not a statement". The style lint passes because it checks only that a docstring is present. | `Defs.lean` at head, lines 139, 152, 162, 172 and 184. | State the formula, e.g. *"`PACLearnsUnder D C m L ε δ` holds iff `1 − δ ≤ accuracyProb D (C i) m L ε` for every `i`."* |
| F9 | minor | `InformationTheory/Samples.lean` · imports | **Layering.** `Samples.lean` imports `Extractors`, which imports `Entropy` and `LeftoverHash`, only to get `FinDist.probTrue` and `probTrue_eq` (defined at `Extractors.lean:62` and `:78` on `main`). So `FinDist.expect`, `FinDist.iid` and the whole PAC layer depend on the leftover-hash and extractor development. The `probTrue` API is now split across `Extractors.lean` and `Samples.lean`, and neither is `FinDist.lean`. Policy §1 (Layering, Helpers) asks for the opposite. | `git grep` at the base: `probTrue` is defined only in `Extractors.lean`. `Samples.lean` uses nothing else from that file's import closure. | In this PR or a scheduled follow-up, move `FinDist.probTrue`/`probTrue_eq` into `FinDist.lean` (or a `FinDist` basic file) next to `expect`, and make `Samples.lean` import only `FinDist`. If deferred, record it in the dedup/refactor queue. |
| F10 | note | Debt (failure mode 5) | **No duplication of proved material found.** At the base I searched all of `TCSlib/` for expectation-like definitions and found no prior `expect`, complement rule, `probTrue_true` or i.i.d./pi construction on `FinDist`. `BooleanAnalysis.Hypercontractivity.FiniteProduct` has `mass = ∏ weight` and `expect f = ∑ x, mass x * f x`, the same formulas as `iid` and `expect`. It lives on a different carrier with strictly positive weights (`weight_pos`), so a `FinDist` with null points does not embed. The pack anticipates this. Mathlib's `Finset.expect` (the uniform average) parallels `(uniform α).expect`. | `git grep` at `7d36bbc`; `Products/Basic.lean:137–161`. | None required. Add a bridge lemma only when a consumer needs one. |
| F11 | note | `InformationTheory/Samples.lean` · `expect_le_add_of_le_one` | Both hypotheses are right and necessary. Without `ε ≥ 0`: take `f ≡ 1` and `ε = −1`, giving `1 ≤ 0`. Without `f ≤ 1`: take `f ≡ 2` and `ε = 0`, giving `2 ≤ 1`. No lower bound on `f` is needed, so the docstring's "`[0, 1]`-valued" (also in the module header) understates the theorem. The statement is stronger than described, which is harmless. This is not Markov's inequality, despite the design note's "Markov on the error": Markov goes from an expectation to a tail bound, and this goes from a tail bound to an expectation. | Pointwise argument as in the sketch; the counterexamples above. | Optionally say "with values at most 1" and fix the design-note wording. |
| F12 | note | `PAC/Prediction.lean` · `expectedErr_le_of_pacLearnsUnder`, `not_weakLearnsUnder_of_predictAdv_le`, module docstring | (i) **The bound has slack.** The same argument gives `E[err] ≤ ε + (1 − ε)δ`, so weak learning gives advantage at least `γ' − δ(½ + γ')`. That roughly doubles the admissible `δ` for small `γ'`, and it is tight at `γ' = ½` (A4). (ii) The hypothesis `predictAdv ≤ γ` is two-sided. The one-sided `predictSuccess ≤ ½ + γ` suffices, which is harmless for a PRF. (iii) The module docstring's "expected error at most ε + δ" omits `ε ≥ 0`, which the theorems carry and which is needed: with `ε < 0` and `δ ≥ 1`, `PACLearnsUnder` holds while the expected error is 1. | Exact checks: both bounds hold on 300 random instances; A4. | Optional strengthening. Add "for `ε ≥ 0`" to the module docstring. |
| F13 | note | `InformationTheory/Samples.lean` · `iid` | `iid p m` is the `m`-fold product (Q5), and `m = 0` gives a point mass. The PR has no lemma relating `iid` to `prod` (for example `iid p (m+1)` against `p.prod (iid p m)` via `Fin.cons`/`Fin.snoc`), no marginal lemma, and no lemma on expectations over `iid`. Layer 2's example-oracle bridge draws one example per query and will need such a decomposition. Under the no-unfolding rule it would otherwise have only `iid_apply` to work from. | Layer-2 plan in the design note, steps 1–2. | Add the decomposition when layer 2 is briefed, not now. |
| F14 | note | `Samples.lean` · `iid`, `## References` | As I recall it, [SSBD14] introduces the i.i.d. assumption and the notation `S ∼ D^m` in ch. 2 (§2.3.1, "The i.i.d. assumption"), and Def 3.1 uses it. The `[SSBD14, §3.1]` location for `S ~ D^m` should be checked. `[Vad12, §6.1]` appears in `Samples.lean`'s References but no declaration in the file cites it. | From memory; the book was not provided. | Verify the location. Drop or use the `[Vad12]` entry. |
| F15 | note | Attestations | Checked mechanically (section 6): the bundle matches the head, the diff is six files, there is no `sorry`, the theorem count is 13 + 14 + 11 = 38 (matching the axiom attestation), and the line counts are 152/228/227. The pack says "the five new or changed modules" were elaborated, but six files changed. `TCSlib.lean` is presumably the one excluded. | `git diff --stat 7d36bbc 44d27f3`. | Name the five modules in the evidence log, and say whether the root `TCSlib.lean` was built (CI builds only what it reaches). |
| F16 | note | Audit limitation · `predictSuccess` against [PS10, p. 179] | I could not read p. 179 (see section 0). Three points depend on its wording: "a new sample" (fresh and independent, or required to be distinct from the examples), "for a random `i`", and "better than `½ + ε`". The formal reading agrees with the design note's transcription and with the layer-2 proof route, which charges the event that the fresh point was already sampled. | Not applicable. | A maintainer should confirm the p. 179 wording before closing. If [PS10] requires `x ∉ {x_j}`, the bridge is to the independent-point game, and that must be declared as a deviation. |

## 2. Definitions: my restatement before reading the docstring, then the comparison

| Definition | My restatement | Docstring agrees? |
|---|---|---|
| `FinDist.expect p f` | The `p`-weighted sum `∑ₐ p(a)·f(a)`. | Yes. |
| `FinDist.iid p m` | A distribution on `Fin m → α` giving the tuple `s` mass `∏ⱼ p(sⱼ)`: the product of `m` copies of `p`. `m = 0` gives unit mass on the empty tuple. | Yes. The citation location is F14. |
| `PAC.err D h c` | The `D`-mass of the disagreement set `{x : h x ≠ c x}`. This is KV94's `error(h)` and SSBD's `L_{D,f}(h)`. | Yes. |
| `PAC.label c s` | The tuple `((sⱼ, c sⱼ))ⱼ`, which is what `EX(c, D)` returns. | Yes. |
| `PAC.accuracyProb D c m L ε` | The probability, over `s ∼ D^m` and independent uniform coins `r`, that the hypothesis `L(label c s, r)` has `D`-error at most `ε` against `c`. | Yes. |
| `PAC.PACLearnsUnder D C m L ε δ` | For every index `i`, the accuracy probability for target `C i` is at least `1 − δ`. | Yes. No tag or deviation (F6); parameter ranges (F2). |
| `PAC.PACLearns C m L ε δ` | `PACLearnsUnder` for every `D : FinDist X`. | Yes, with "at fixed `m, ε, δ`". Undeclared: improper hypotheses (F3) and the coin model (F4). |
| `PAC.WeakLearnsUnder D C m L γ δ` | `PACLearnsUnder` at accuracy `½ − γ`. | Yes. Deviations from KV94 §4.1 are not stated (F6). |
| `PAC.WeakLearns C m L γ δ` | `WeakLearnsUnder` for every `D`. | Yes, with F6. |
| `PAC.PACLearnable C m ε δ` | There is a finite nonempty coin type `ρ' : Type` and a learner `L` with `PACLearns C m L ε δ`. (The universe-0 restriction is harmless: every finite type is equivalent to some `Fin n`.) | The prose is right, but the comparison with the sources is wrong (F1). |
| `PAC.trialDist X I ρ m` | The independent triple: uniform index, `m` uniform examples, uniform coins. | Yes. |
| `PAC.predictSuccess C m L` | The probability, over a trial and an independent uniform fresh `x`, that the hypothesis `L(label (C i) s, r)` evaluated at `x` equals `C i x`. | Yes. The reading is declared only at module level (F7). |
| `PAC.predictAdv C m L` | The distance from `predictSuccess` to `½`, i.e. the two-sided advantage. | Yes. |
| `PAC.expectedErr C m L` | The expectation over a trial of the uniform error of the hypothesis `L(label (C i) s, r)` against `C i`. | Yes. |

All 14 definitions ship with an `_eq`, `_iff` or `_apply` lemma, as the "definitions land with their lemmas" rule
requires. F8 concerns the wording of five of them.

## 3. Theorems: is the statement what the docstring claims?

**`Samples.lean` (13).**

| Theorem | Verdict |
|---|---|
| `expect_eq`, `iid_apply` | Equation lemmas (`rfl`); match their docstrings. |
| `expect_const`, `expect_add`, `expect_const_mul`, `expect_one_sub` | `E[c] = c`, additivity, homogeneity, and `E[1 − f] = 1 − E[f]`. Exactly as stated. |
| `expect_le_expect`, `expect_nonneg` | Monotonicity and nonnegativity. As stated. |
| `probTrue_eq_expect` | `Pr[D] = E[1_D]`. As stated. |
| `probTrue_not` | `Pr[¬D] = 1 − Pr[D]`. As stated. |
| `probTrue_true` | The always-accepting test has probability 1. As stated. |
| `expect_prod` | Fubini for `p.prod q`. As stated. |
| `expect_le_add_of_le_one` | True. Both hypotheses are necessary. The docstring understates its generality (F11). |

**`PAC/Defs.lean` (14).**

| Theorem | Verdict |
|---|---|
| `err_eq`, `label_apply`, `accuracyProb_eq`, five `_iff` | `rfl` equations, correct. The `_iff` docstrings are bare labels (F8). |
| `err_nonneg`, `err_le_one`, `err_self` | `0 ≤ err ≤ 1` and `err(c, c) = 0`. As stated. |
| `err_not` | `err(¬h, c) = 1 − err(h, c)`. As stated. |
| `pacLearns_const` | If every `C i` equals `c₀`, the learner that always outputs `c₀` learns from 0 examples for every `ε, δ ≥ 0`. As stated. It also covers empty `I`, and it proves `PACLearns` of an explicit learner, which is stronger than the docstring's "PAC-learnable". |
| `not_pacLearnsUnder_of_neg` | For nonempty `I`, `ε < 0` and `δ < 1`: no learner. The statement is right. The non-vacuity it is cited for is out of range (F2). |

**`PAC/Prediction.lean` (11).**

| Theorem | Verdict |
|---|---|
| `trialDist_eq`, `predictSuccess_eq`, `predictAdv_eq`, `expectedErr_eq` | `rfl` equations, correct. |
| `predictSuccess_eq_one_sub_expectedErr` | Exactly true as stated (Q4). |
| `expectedErr_le_of_pacLearnsUnder` | Learning under uniform `D` at `(ε, δ)` with `ε ≥ 0` gives expected error at most `ε + δ`. True; `ε ≥ 0` is needed; not tight (F12). |
| `one_sub_sub_le_predictSuccess` | Success at least `1 − ε − δ`. As stated. |
| `sub_le_predictAdv_of_weakLearnsUnder` | For `γ ≤ ½`, advantage at least `γ − δ`. As stated. Tight at `γ = ½` (A4). |
| `not_weakLearnsUnder_of_predictAdv_le` | Advantage at most `γ`, together with `γ + δ < γ' ≤ ½`, gives `¬ WeakLearnsUnder U C m L γ' δ`. As stated. On the use of `δ`, see F5. |
| `expect_err_coin` | A fair coin between the two constant hypotheses has expected error `½`. As stated. |
| `predictSuccess_coin` | The learner that outputs its coin has success exactly `½`. As stated. This gives non-vacuity of the game. |

## 4. Adversarial instantiations

| # | Instantiation | Outcome |
|---|---|---|
| A1 | Degenerate parameters. | The predicates are trivially true at `ε ≥ 1`, at `δ ≥ 1`, at `γ ≤ −½` (weak learning), and for empty `I`. They are false at `ε < 0` or `δ < 0` when `I` is nonempty. Empty `X` makes `PACLearns` vacuous (declared). `m = 0` and a singleton `ρ` are meaningful. Undeclared ranges: **F2**. |
| A2 | `X = Bool`, `C` = all 4 concepts, `m = 0`, `ε = ¼`, `δ = ½`. | No learner: under uniform `D` the hypothesis ignores the target, err ≤ ¼ forces err = 0, and the four accuracies sum to 1. At `m = 9`, ERM learns, so the class is source-learnable. Fixed-`m` impossibility is not source impossibility: **F1**. |
| A3 | PRF-shaped class with `2ⁿ` keys. | Information-theoretically `PACLearnable` at a polynomial `m` (ERM). So Thm 179.1 cannot be stated as `¬ PACLearnable`: **F1**. |
| A4 | `X = {a}`, two constant concepts, `m = 1`, label-flipping learner with `ρ = Bool`. | `predictAdv = 0` exactly, yet `WeakLearnsUnder U C 1 L γ' ½` holds for `γ' ∈ {½, 1/10}`. The confidence condition is essential: **F5**. It also shows `sub_le_predictAdv…` is tight at `γ' = ½`. |
| A5 | `D(a) = 1/√3`, three concepts, `m = 1`, `ε = 1/10`, `δ = 1/3`. | Only irrational mixing achieves the threshold, so finite uniform coins cannot: **F4**. |
| A6 | A one-point `X` with `m ≥ 1`, or more generally `m` comparable to `card X`. | The examples can cover `X`. Under a "fresh point not among the examples" reading the game would be undefined. The independent reading is total, and the bridge holds exactly. A memorizing learner wins on coincidences, and its hypothesis's `err` accounts for that exactly. This supports the formal reading (Q3). |
| A7 | Indices with duplicate concepts (several keys giving the same `C i`). | The game is uniform over **indices**, not over distinct concepts. That matches [PS10]'s "random `i`", the PRF key. Correct. |
| A8 | 300 random exact instances (`card X ≤ 3`, `card I ≤ 4`, `m ≤ 2`, `card ρ ≤ 3`, random learner tables). | The bridge identity holds exactly. Both the stated bound `ε + δ` and the tight bound `ε + (1 − ε)δ` hold. |

## 5. Answers to the pack's specific questions

1. **PAC learning.**
   - The core structure matches [KV94, §1.2.1, Def 1] and [SSBD14, Def 3.1]: for every target and every `D`,
     with probability at least `1 − δ` over i.i.d. labelled examples and the learner's coins, error at most `ε`.
     The error is the sources' error.
   - SSBD's realizable assumption (a target `f` agreeing with some `h ∈ H` off a `D`-null set) is equivalent to
     taking the target to be `C i`. Examples outside `supp D` have `D^m`-mass 0, and `err` ignores null points.
   - Beyond the declared fixed-parameter deviation, three deviations are undeclared: improper hypotheses (F3),
     unrestricted `ε, δ` (F2), and finite uniform coins (F4).
   - **The declared deviation is stated only in the module docstring, not on `PACLearnable`.** "Weaker, so
     impossibility results are stronger" is **not correct** as stated (F1). It holds only for an impossibility
     over all `m` up to the claimed sample bound, and over a finite `X` the "all `m`" form never holds in range.
2. **Weak learning.** Yes: `WeakLearnsUnder` is [KV94, §4.1]'s accuracy requirement (error at most `½ − γ`) at a
   fixed distribution. It differs in having fixed `D`, `γ` and `δ`, with `γ` unconstrained (F6). Fixing `D` makes
   it weaker, which is the right direction for Thm 179.1(c).
3. **The prediction game.** Yes, as far as I can check without the PDF. The game draws `i ∼ U_I`, examples
   `s ∼ U_X^m` labelled by `C i`, coins `r ∼ U_ρ`, and a fresh `x ∼ U_X`, all independent, and it is won when
   `L(label (C i) s, r)(x) = C i x`. The fresh point **may** coincide with an example. That is the "uniform and
   independent" reading (the classical prediction model). It is the only reading defined on every finite domain
   (A6), and it is the one the layer-2 route assumes. The source's wording was not verified (F16), and the reading
   should be declared on the declaration (F7).
4. **The bridge and its consequences.**
   - `predictSuccess_eq_one_sub_expectedErr` is exactly true as stated (proof idea checked, and A8).
   - `not_weakLearnsUnder_of_predictAdv_le` says exactly this: advantage at most `γ` rules out weak learning
     with `γ' > γ + δ`, for `γ' ≤ ½`.
   - That is what Thm 179.1(c) needs **provided (c) fixes `δ` below the gap**, e.g. `δ = (γ' − γ)/2`. That is
     enough to refute KV94-style weak learning. For constant `δ` the bridge provably cannot deliver it (A4), and
     confidence boosting is needed (F5).
5. **`Samples.lean`.**
   - `FinDist.iid` is the product of `m` copies, with mass `∏ⱼ p(sⱼ)`; `m = 0` gives a point mass. It lacks
     decomposition lemmas for later use (F13).
   - `expect_le_add_of_le_one` has the right hypotheses (`f ≤ 1`, `ε ≥ 0`), both necessary. No lower bound on `f`
     is needed (F11).

## 6. Attestations and repository cross-checks

| Attestation | What I checked | Result |
|---|---|---|
| Bundle is the PR at `44d27f3` | Byte comparison of all 8 bundle files against `git show 44d27f3:<path>`. | Identical. |
| Diff scope | `git diff --stat 7d36bbc 44d27f3`. | 6 files, +646: the 3 new files, the `PAC.lean` facade, `InformationTheory.lean` (+5), `TCSlib.lean` (+1). |
| No `sorry` | grep over the three new files. | None. |
| 38 theorems within the standard axioms | Theorem count per file: 13 + 14 + 11 = 38. | The count matches. Axioms not rerun. |
| Line counts 152/228/227 | `wc` on the head versions. | They match. |
| Elaboration, lint | Not rerun. | "Five modules" against six changed files (F15). |
| Policy header, facade, exports, statement prose, proof sketches | Read. | Compliant, except F8 (bare `_iff` labels) and F9 (layering). |

## Appendix A: summary of severities

- **Major (1):** F1.
- **Minor (8):** F2, F3, F4, F5, F6, F7, F8, F9.
- **Note (7):** F10, F11, F12, F13, F14, F15, F16.
- The gate closes at 0 blockers and 0 majors, so the remaining step is F1, a docstring rewrite.

## Appendix B: derivations

**A2 (all concepts on `Bool`, `m = 0`).**
- Under uniform `D`, `err(h, c) ∈ {0, ½, 1}`, so `err ≤ ¼` exactly when `h = c`.
- With `m = 0` the hypothesis `h_r` depends only on the coin `r`. So
  `∑_c accuracyProb(c) = ∑_c Pr_r[h_r = c] = 1`, and some target has accuracy at most `¼ < ½ = 1 − δ`.
- More generally, with `|X| = k`, all `2^k` concepts, `m = 0`, `ε < 1/k` and `δ < 1 − 2^{−k}`, no learner exists.
- ERM succeeds by the union bound once `4(1 − ¼)^m ≤ ½`, i.e. from `m = 8` on. [SSBD14]'s bound
  `⌈ln(4/δ)/ε⌉ = ⌈4 ln 8⌉ = 9` is the figure quoted in F1.

**A4 (label flipper).**
- `X = {a}`, `C₀ ≡ false`, `C₁ ≡ true`, `m = 1`, `ρ = Bool`. The learner outputs the observed label on
  `r = false` and its negation on `r = true`.
- `err` is 0 or 1 with probability ½ each, so `accuracyProb(½ − γ') = ½` for every `γ' ≤ ½`. Hence
  `WeakLearnsUnder U C 1 L γ' ½`.
- The fresh point is `a`, so success is `Pr[r = false] = ½` and `predictAdv = 0`.
- In general, flipping with probability `δ` gives advantage `½ − δ = γ' − δ` at `γ' = ½`. So
  `sub_le_predictAdv_of_weakLearnsUnder` is tight there.

**A5 (irrational mixing).** Setup:
- `X = {a, b}`, `p = D(a) = 1/√3`.
- Concepts, written as their values at `(a, b)`: `c₁ = (0,0)`, `c₂ = (0,1)`, `c₃ = (1,1)`.
- `m = 1`, `ε = 1/10 < min(p, 1 − p)`, so a hypothesis is accurate for `c` iff it equals `c`.

Analysis:
- Samples `(b,0)` and `(a,1)` identify `c₁` and `c₃`.
- On `(a,0)` the learner outputs `c₂` with probability `q`; on `(b,1)` it outputs `c₂` with probability `r`.
  The other outputs on these samples can only help the other consistent concept.
- Writing `u = p(1 − q_{c₁})` and `v = (1 − p)(1 − r_{c₃})`, accuracy is at most `1 − u` for `c₁`, at most
  `1 − v` for `c₃`, and at most `u + v` for `c₂`.
- All three can be at least `⅔ = 1 − δ` only if `u = v = ⅓`, with every remaining mass on the consistent
  concepts. That forces `q = 1/(3p) = 1/√3`, which is irrational.
- A learner with uniform coins on a finite `ρ` has rational `q = k/|ρ|`, so none reaches `δ = 1/3`.
- A randomized learner with bias `1/√3` meets the threshold exactly (verified in exact ℚ(√3) arithmetic).

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

## ===== evidence-r2/repair.diff.txt =====

diff --git a/TCSlib/InformationTheory/Samples.lean b/TCSlib/InformationTheory/Samples.lean
index 6b206664..a416dd85 100644
--- a/TCSlib/InformationTheory/Samples.lean
+++ b/TCSlib/InformationTheory/Samples.lean
@@ -28,14 +28,13 @@ an iterated expectation.
 * `FinDist.expect_le_expect`, `FinDist.expect_const`, `FinDist.expect_add`,
   `FinDist.expect_const_mul`, `FinDist.expect_one_sub`: linearity and monotonicity.
 * `FinDist.probTrue_not`: the complement rule `Pr[¬D] = 1 − Pr[D]`.
-* `FinDist.expect_le_add_of_le_one`: a function with values in `[0, 1]` has expectation at most
+* `FinDist.expect_le_add_of_le_one`: a function with values at most `1` has expectation at most
   `ε + Pr[f > ε]`, for `ε ≥ 0`.
 
 ## References
 
 * [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
   Algorithms*, Cambridge University Press, 2014, §3.1 (the i.i.d. sample `S ~ D^m`).
-* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1.
 -/
 
 namespace TCSlib.InformationTheory
@@ -110,8 +109,9 @@ theorem expect_prod (p : FinDist α) (q : FinDist β) (f : α × β → ℝ) :
   simp only [expect_eq, Fintype.sum_prod_type, prod_apply, Finset.mul_sum]
   exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
 
-/-- **A `[0, 1]`-valued function has expectation at most `ε + Pr[f > ε]`**, for `ε ≥ 0`: on the
-event `f ≤ ε` it contributes at most `ε`, elsewhere at most `1`.
+/-- **A function with values at most `1` has expectation at most `ε + Pr[f > ε]`**, for
+`ε ≥ 0`: on the event `f ≤ ε` it contributes at most `ε`, elsewhere at most `1`. No lower bound
+on `f` is needed.
 
 **Proof sketch.** Pointwise `f a ≤ ε + 1_{f a > ε}`, since `f a ≤ 1` and `ε ≥ 0`; take expectations
 (`expect_le_expect`, `expect_add`, `expect_const`, `probTrue_eq_expect`). -/
diff --git a/TCSlib/LearningTheory/PAC.lean b/TCSlib/LearningTheory/PAC.lean
index 39dc0e7f..94807ae1 100644
--- a/TCSlib/LearningTheory/PAC.lean
+++ b/TCSlib/LearningTheory/PAC.lean
@@ -19,9 +19,10 @@ bridge to PAC learning.
 ## Contents
 
 * `TCSlib.LearningTheory.PAC.Defs`: error, labelled samples, PAC, weak and fixed-distribution
-  learning, PAC-learnability at fixed parameters.
+  learning, for a given learner at fixed parameters.
 * `TCSlib.LearningTheory.PAC.Prediction`: the prediction game; success `= 1 − E[err]`, so
-  a small prediction advantage rules out weak learning under the uniform distribution.
+  a small prediction advantage rules out weak learning under the uniform distribution, for that
+  learner, at confidence below the gap.
 
 ## References
 
diff --git a/TCSlib/LearningTheory/PAC/Defs.lean b/TCSlib/LearningTheory/PAC/Defs.lean
index 283229c3..00f04897 100644
--- a/TCSlib/LearningTheory/PAC/Defs.lean
+++ b/TCSlib/LearningTheory/PAC/Defs.lean
@@ -23,13 +23,29 @@ independent examples, and PAC, weak and fixed-distribution learning.
   `L : (Fin m → X × Bool) → ρ → (X → Bool)`; its coins are uniform on the finite type `ρ`.
 - Distributions are `InformationTheory.FinDist`: real-valued, on a finite type.
 
-**Deviations from [KV94, §1.2] and [SSBD14, Def 3.1].**
-- **Fixed parameters.** `PACLearns C m L ε δ` fixes the sample size `m`, the accuracy `ε` and
-  the confidence `δ`. The sources ask for one algorithm that works for all `ε, δ`, with a sample
-  size polynomial in `1/ε`, `1/δ` (and, in [KV94], in the instance size), and efficiency is part
-  of [KV94]'s definition. Here `PACLearnable C m ε δ` asks only for some learner at the given
-  parameters. That notion is weaker, so impossibility results stated with it are stronger.
-  Efficiency is layer 2's (the cryptographic statement of [PS10, Thm 179.1]).
+**Deviations from [KV94, §1.2.1] and [SSBD14, Def 3.1].**
+- **Learners at fixed parameters, not learnability of a class.** `PACLearns C m L ε δ` is the
+  condition the sources place on one learner `L` at one sample size `m`, accuracy `ε` and
+  confidence `δ`. Their learnability asks for one algorithm that meets it for every
+  `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`) on `m ≥ m_H(ε, δ)` examples, for some function `m_H`;
+  [KV94] also bounds the running time, and so `m`, by a polynomial in `1/ε`, `1/δ` and the
+  instance size. That class-level notion is not defined here: over a finite `X` every class has
+  it, since a learner that outputs a concept of the class consistent with its sample succeeds
+  once `m ≥ (|X| ln 2 + ln (1/δ)) / ε`. Impossibility is therefore stated per learner, at that
+  learner's `m`, `ε`, `δ` (`Prediction.lean`; for efficient learners, layer 2 and
+  [PS10, Thm 179.1]). This is faithful: a source learner run on `m ≥ m_H(ε, δ)` examples is
+  such an `L`.
+- **Unrestricted parameters.** `ε`, `δ` and the weak-learning edge `γ` are arbitrary reals, where
+  the sources take `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`) and `γ > 0`. The docstrings of the
+  predicates list the degenerate cases.
+- **Improper hypotheses.** A learner may output any `X → Bool` (representation-independent
+  learning). [KV94, §1.2.1] requires `h ∈ C`; [SSBD14, Def 3.1] does not. A refutation is
+  stronger without the restriction.
+- **Coins.** A learner's coins are uniform on a finite type. This models every fair-coin
+  algorithm with bounded running time ([KV94]), and [SSBD14]'s deterministic learners are the
+  case `ρ = Unit`. A learner that needs an irrational mixing probability is not of this form. At
+  a fixed `D` and an exactly tight `δ` this can matter, so a statement `¬ ∃ ρ L, …` rules out
+  fair-coin learners, not every randomized learner.
 - **Finite domains.** `X` is a finite type, so the "instance size" of [KV94] is not modelled.
   With `X` empty there is no distribution on `X`, so every PAC statement holds vacuously.
 
@@ -39,19 +55,22 @@ independent examples, and PAC, weak and fixed-distribution learning.
 * `PAC.label c s`: the sample `s` labelled by `c`.
 * `PAC.accuracyProb D c m L ε`: the probability, over `m` examples from `D` and the coins, that
   the learner's hypothesis has error at most `ε`.
-* `PAC.PACLearnsUnder D C m L ε δ`, `PAC.PACLearns C m L ε δ`: PAC learning under a fixed
-  distribution and under every distribution.
-* `PAC.WeakLearnsUnder`, `PAC.WeakLearns`: weak learning, accuracy `½ − γ` [KV94, §4].
-* `PAC.PACLearnable C m ε δ`: some learner PAC-learns `C` at these parameters.
+* `PAC.PACLearnsUnder D C m L ε δ`, `PAC.PACLearns C m L ε δ`: the learner `L` PAC-learns `C`
+  under a fixed distribution and under every distribution, at fixed `m`, `ε`, `δ`.
+* `PAC.WeakLearnsUnder`, `PAC.WeakLearns`: weak learning at a fixed edge `γ`, accuracy `½ − γ`
+  [KV94, §4.1].
 
 ## Main results
 
 * `PAC.err_nonneg`, `PAC.err_le_one`, `PAC.err_self`, `PAC.err_not`: basic properties; `err_not`
   says the complementary hypothesis has the complementary error.
-* `PAC.pacLearns_const`: a class with one concept is PAC-learnable from no examples
-  (non-vacuity).
+* `PAC.pacLearns_const`: the constant learner PAC-learns a class with one concept from no
+  examples, at every `ε, δ ≥ 0` (non-vacuity).
 * `PAC.not_pacLearnsUnder_of_neg`: no learner reaches a negative accuracy with confidence
-  `δ < 1` (the definition does not hold trivially).
+  `δ < 1` (a witness outside the sources' range).
+* `PAC.not_pacLearnsUnder_const_pair`: with no examples, no learner learns the two constant
+  concepts on a one-point domain at accuracy `ε < 1` and confidence `δ < ½` (a witness inside
+  the sources' range).
 
 ## References
 
@@ -124,73 +143,94 @@ noncomputable def accuracyProb (D : FinDist X) (c : X → Bool) (m : ℕ)
   ((D.iid m).prod (FinDist.uniform ρ)).probTrue
     fun sr => decide (err D (L (label c sr.1) sr.2) c ≤ ε)
 
-/-- The accuracy probability as a probability over the examples and the coins. -/
+/-- The accuracy probability is the probability, over examples `s ← D^m` and uniform coins
+`r ← ρ`, of the event `err_D(L(s labelled by c, r), c) ≤ ε`. -/
 theorem accuracyProb_eq (D : FinDist X) (c : X → Bool) (m : ℕ)
     (L : (Fin m → X × Bool) → ρ → X → Bool) (ε : ℝ) :
     accuracyProb D c m L ε = ((D.iid m).prod (FinDist.uniform ρ)).probTrue
       (fun sr => decide (err D (L (label c sr.1) sr.2) c ≤ ε)) := rfl
 
-/-- **PAC learning under the distribution `D`** (fixed-distribution learning): for every concept
-of the class, with probability at least `1 − δ` the hypothesis has error at most `ε`. -/
+/-- **PAC learning under the distribution `D`** (fixed-distribution learning), by the learner `L`
+at fixed `m`, `ε`, `δ`: for every concept `C i` of the class, with probability at least `1 − δ`
+over `m` examples from `D` labelled by `C i` and the learner's coins, the hypothesis has error at
+most `ε` under `D`. This is the fixed-distribution variant of [KV94, §1.2.1] /
+[SSBD14, Def 3.1] (the case [PS10, §8.1] needs); it is weaker than distribution-free learning.
+
+The parameters are unrestricted reals; the sources take `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`).
+Outside that range the predicate is degenerate: every learner satisfies it when `δ ≥ 1`, when
+`ε ≥ 1` and `δ ≥ 0`, or when `I` is empty; no learner satisfies it when `I` is nonempty and
+either `δ < 0`, or `ε < 0` and `δ < 1`. -/
 def PACLearnsUnder (D : FinDist X) (C : I → X → Bool) (m : ℕ)
     (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) : Prop :=
   ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε
 
-/-- `PACLearnsUnder` unfolded. -/
+/-- `PACLearnsUnder D C m L ε δ` holds iff `1 − δ ≤ accuracyProb D (C i) m L ε` for every
+index `i`. -/
 theorem pacLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
     (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) :
     PACLearnsUnder D C m L ε δ ↔ ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε := Iff.rfl
 
-/-- **PAC learning** [KV94, §1.2], [SSBD14, Def 3.1], at fixed `m`, `ε`, `δ`: for every
+/-- **A PAC learner at fixed parameters** [KV94, §1.2.1], [SSBD14, Def 3.1]: for every
 distribution `D` on `X` and every concept `C i`, with probability at least `1 − δ` over `m`
 examples from `D` labelled by `C i` and the learner's coins, the hypothesis has error at most `ε`
-under `D`. -/
+under `D`. The sources require this of one algorithm for every `ε, δ` and every large enough `m`.
+Here `m`, `ε`, `δ` are fixed, `ε` and `δ` are unrestricted reals, the hypothesis may be any
+`X → Bool`, and the coins are uniform on the finite type `ρ` (module deviations).
+
+Outside the sources' range `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`) the predicate is degenerate: every
+learner satisfies it when `δ ≥ 1`, when `ε ≥ 1` and `δ ≥ 0`, or when `I` or `X` is empty; no
+learner satisfies it when `I` and `X` are nonempty and either `δ < 0`, or `ε < 0` and `δ < 1`. -/
 def PACLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) :
     Prop :=
   ∀ D : FinDist X, PACLearnsUnder D C m L ε δ
 
-/-- `PACLearns` unfolded. -/
+/-- `PACLearns C m L ε δ` holds iff `PACLearnsUnder D C m L ε δ` holds for every distribution
+`D` on `X`. -/
 theorem pacLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
     (ε δ : ℝ) : PACLearns C m L ε δ ↔ ∀ D, PACLearnsUnder D C m L ε δ := Iff.rfl
 
-/-- **Weak learning under `D`** [KV94, §4]: PAC learning under `D` with accuracy `½ − γ`, a
-hypothesis better than a fair coin by `γ`. -/
+/-- **Weak learning under `D`** [KV94, §4.1], by the learner `L` at fixed `m`, `γ`, `δ`: PAC
+learning under `D` with accuracy `½ − γ`, a hypothesis better than a fair coin by the edge `γ`.
+[KV94] asks for this under every distribution, at an edge `γ = 1/p(n, size(c))`, and for every
+confidence `δ`, in time polynomial in `1/δ`; here `D`, the real edge `γ` and the confidence `δ`
+are fixed. Each relaxation makes the predicate weaker, so a refutation for a given learner is
+stronger.
+
+Only `γ > 0` is weak learning. The parameters are unrestricted reals: every learner satisfies the
+predicate when `δ ≥ 1`, when `γ ≤ −½` and `δ ≥ 0`, or when `I` is empty; no learner satisfies it
+when `I` is nonempty and either `δ < 0`, or `γ > ½` and `δ < 1`. -/
 def WeakLearnsUnder (D : FinDist X) (C : I → X → Bool) (m : ℕ)
     (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) : Prop :=
   PACLearnsUnder D C m L (1 / 2 - γ) δ
 
-/-- `WeakLearnsUnder` unfolded. -/
+/-- `WeakLearnsUnder D C m L γ δ` holds iff `PACLearnsUnder D C m L (½ − γ) δ`: PAC learning
+under `D` at accuracy `½ − γ`. -/
 theorem weakLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
     (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
     WeakLearnsUnder D C m L γ δ ↔ PACLearnsUnder D C m L (1 / 2 - γ) δ := Iff.rfl
 
-/-- **Weak learning** [KV94, §4]: under every distribution, accuracy `½ − γ`. -/
+/-- **Weak learning** [KV94, §4.1], by the learner `L` at fixed `m`, `γ`, `δ`: under every
+distribution `D` on `X`, PAC learning with accuracy `½ − γ` (`WeakLearnsUnder`). [KV94] takes
+the edge `γ = 1/p(n, size(c))` and asks for every confidence `δ`, in time polynomial in `1/δ`;
+here the real edge `γ` and the confidence `δ` are fixed. Each relaxation makes the predicate
+weaker, so a refutation for a given learner is stronger.
+
+Only `γ > 0` is weak learning. The parameters are unrestricted reals: every learner satisfies the
+predicate when `δ ≥ 1`, when `γ ≤ −½` and `δ ≥ 0`, or when `I` or `X` is empty; no learner
+satisfies it when `I` and `X` are nonempty and either `δ < 0`, or `γ > ½` and `δ < 1`. -/
 def WeakLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
     Prop :=
   ∀ D : FinDist X, WeakLearnsUnder D C m L γ δ
 
-/-- `WeakLearns` unfolded. -/
+/-- `WeakLearns C m L γ δ` holds iff `WeakLearnsUnder D C m L γ δ` holds for every distribution
+`D` on `X`. -/
 theorem weakLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
     (γ δ : ℝ) : WeakLearns C m L γ δ ↔ ∀ D, WeakLearnsUnder D C m L γ δ := Iff.rfl
 
-omit [Fintype ρ] [Nonempty ρ] in
-/-- **PAC-learnability at fixed parameters**: some learner, with finite nonempty coins, learns `C`
-from `m` examples with accuracy `ε` and confidence `δ`. -/
-def PACLearnable (C : I → X → Bool) (m : ℕ) (ε δ : ℝ) : Prop :=
-  ∃ (ρ' : Type) (_ : Fintype ρ') (_ : Nonempty ρ') (L : (Fin m → X × Bool) → ρ' → X → Bool),
-    PACLearns C m L ε δ
-
-omit [Fintype ρ] [Nonempty ρ] in
-/-- `PACLearnable` unfolded. -/
-theorem pacLearnable_iff (C : I → X → Bool) (m : ℕ) (ε δ : ℝ) :
-    PACLearnable C m ε δ ↔
-      ∃ (ρ' : Type) (_ : Fintype ρ') (_ : Nonempty ρ')
-        (L : (Fin m → X × Bool) → ρ' → X → Bool), PACLearns C m L ε δ := Iff.rfl
-
 /-! ### Non-vacuity -/
 
-/-- **A class with one concept is PAC-learnable from no examples** (non-vacuity of
-`PACLearns`): if every `C i` is `c₀`, the learner that outputs `c₀` has error `0`, so it learns
+/-- **The constant learner PAC-learns a class with one concept from no examples** (non-vacuity
+of `PACLearns`): if every `C i` is `c₀`, the learner that outputs `c₀` has error `0`, so it learns
 at every accuracy `ε ≥ 0` and confidence `δ ≥ 0`. -/
 theorem pacLearns_const {C : I → X → Bool} {c₀ : X → Bool} (hC : ∀ i, C i = c₀) {ε δ : ℝ}
     (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
@@ -206,8 +246,8 @@ theorem pacLearns_const {C : I → X → Bool} {c₀ : X → Bool} (hC : ∀ i,
   linarith
 
 /-- **No learner reaches a negative accuracy with confidence `δ < 1`**: the error is
-nonnegative, so the accuracy event is empty and its probability `0 < 1 − δ`. `PACLearns` is
-therefore not trivially satisfied. -/
+nonnegative, so the accuracy event is empty and its probability `0 < 1 − δ`. So
+`PACLearnsUnder` fails at every negative accuracy (a witness outside the sources' range). -/
 theorem not_pacLearnsUnder_of_neg (D : FinDist X) {C : I → X → Bool} [Nonempty I] {m : ℕ}
     (L : (Fin m → X × Bool) → ρ → X → Bool) {ε δ : ℝ} (hε : ε < 0) (hδ : δ < 1) :
     ¬ PACLearnsUnder D C m L ε δ := by
@@ -225,4 +265,51 @@ theorem not_pacLearnsUnder_of_neg (D : FinDist X) {C : I → X → Bool} [Nonemp
   simp at h1
   linarith
 
+/-- **With no examples, no learner tells two concepts apart** (non-vacuity in the sources'
+range): on a one-point domain with the two constant concepts, every learner with `m = 0` fails to
+PAC-learn them under the distribution `D`, at every accuracy `ε < 1` and confidence `δ < ½`.
+
+**Proof sketch.** With no examples the labelled sample is the same for both targets, so the
+hypothesis depends on the coins only. Its error against the constant `b` is `0` when it outputs
+`b` and `1` otherwise, so on every draw it is accurate (error at most `ε < 1`) for at most one of
+the two targets. The two accuracy probabilities therefore sum to at most `1`, while learning
+would make each at least `1 − δ > ½`. -/
+theorem not_pacLearnsUnder_const_pair (D : FinDist Unit)
+    (L : (Fin 0 → Unit × Bool) → ρ → Unit → Bool) {ε δ : ℝ} (hε : ε < 1) (hδ : δ < 1 / 2) :
+    ¬ PACLearnsUnder D (fun (b : Bool) (_ : Unit) => b) 0 L ε δ := by
+  intro h
+  -- an accurate hypothesis agrees with the target at the single point
+  have hagree : ∀ h' c : Unit → Bool, err D h' c ≤ ε → h' () = c () := by
+    intro h' c hle
+    by_contra hne
+    have hall : (fun x => h' x != c x) = fun _ => true := by
+      funext x
+      cases x
+      simpa using hne
+    rw [err_eq, hall, FinDist.probTrue_true] at hle
+    linarith
+  -- with no examples, the labelled sample does not depend on the target
+  have hlab : ∀ (c : Unit → Bool) (s : Fin 0 → Unit), label c s = label (fun _ => true) s :=
+    fun _ _ => Subsingleton.elim _ _
+  -- on every draw, at most one of the two targets is learned accurately
+  have hsum :
+      accuracyProb D (fun _ => true) 0 L ε + accuracyProb D (fun _ => false) 0 L ε ≤ 1 := by
+    rw [accuracyProb_eq, accuracyProb_eq, FinDist.probTrue_eq_expect,
+      FinDist.probTrue_eq_expect, ← FinDist.expect_add]
+    calc _ ≤ ((D.iid 0).prod (FinDist.uniform ρ)).expect (fun _ => 1) :=
+          FinDist.expect_le_expect _ fun sr => ?_
+      _ = 1 := FinDist.expect_const _ _
+    dsimp only
+    rw [hlab (fun _ => false)]
+    generalize L (label (fun _ => true) sr.1) sr.2 = g
+    by_cases ht : err D g (fun _ => true) ≤ ε
+    · have hf : ¬ err D g (fun _ => false) ≤ ε := fun hf => by
+        have := (hagree _ _ ht).symm.trans (hagree _ _ hf)
+        simp at this
+      simp [ht, hf]
+    · by_cases hf : err D g (fun _ => false) ≤ ε <;> simp [ht, hf]
+  have h1 : 1 - δ ≤ accuracyProb D (fun _ => true) 0 L ε := h true
+  have h0 : 1 - δ ≤ accuracyProb D (fun _ => false) 0 L ε := h false
+  linarith
+
 end TCSlib.LearningTheory.PAC
diff --git a/TCSlib/LearningTheory/PAC/Prediction.lean b/TCSlib/LearningTheory/PAC/Prediction.lean
index 3094d5e5..d3abde33 100644
--- a/TCSlib/LearningTheory/PAC/Prediction.lean
+++ b/TCSlib/LearningTheory/PAC/Prediction.lean
@@ -21,11 +21,13 @@ independent; the learner wins when `L(s labelled by C_i, r)(x) = C_i(x)`.
 probability of a correct prediction is `1 − err_U(h, C_i)` for the hypothesis `h = L(s, r)`.
 So the prediction success is `1 − E_{i,s,r}[err_U(L(s, r), C_i)]`
 (`predictSuccess_eq_one_sub_expectedErr`), with no collision issue between the fresh point and
-the sample. A learner that PAC-learns under the uniform distribution with accuracy `ε` and
+the sample. A learner that PAC-learns under the uniform distribution with accuracy `ε ≥ 0` and
 confidence `δ` has expected error at most `ε + δ`, hence prediction success at least `1 − ε − δ`.
 So a learner whose prediction advantage is at most `γ` cannot weakly learn under the uniform
-distribution with `γ' > γ + δ` at confidence `δ` (`not_weakLearnsUnder_of_predictAdv_le`). This is
-how layer 2 turns [PS10, Thm 179.1] into "the class is not weakly learnable".
+distribution with `γ + δ < γ' ≤ ½` at confidence `δ` (`not_weakLearnsUnder_of_predictAdv_le`).
+This is how layer 2 turns [PS10, Thm 179.1] into "no efficient learner weakly learns the class
+under the uniform distribution" (for each learner, at a confidence below the edge).
+Information-theoretically the class is learnable; the hardness is computational.
 
 **Source notes.** [PS10] leaves the sample distribution and "a new sample" implicit; uniform
 and independent is the reading (design note S3d). "Better than `½ + ε`" is the advantage
@@ -42,11 +44,11 @@ and independent is the reading (design note S3d). "Better than `½ + ε`" is the
 
 * `PAC.predictSuccess_eq_one_sub_expectedErr`: **the bridge**, success `= 1 − E[err]`.
 * `PAC.expectedErr_le_of_pacLearnsUnder`, `PAC.one_sub_sub_le_predictSuccess`: PAC learning
-  under the uniform distribution gives expected error at most `ε + δ` and success at least
-  `1 − ε − δ`.
+  under the uniform distribution with accuracy `ε ≥ 0` gives expected error at most `ε + δ` and
+  success at least `1 − ε − δ`.
 * `PAC.sub_le_predictAdv_of_weakLearnsUnder`, `PAC.not_weakLearnsUnder_of_predictAdv_le`: weak
-  learning with `γ'` gives advantage at least `γ' − δ`; so advantage at most `γ` rules out weak
-  learning with `γ' > γ + δ`.
+  learning with `γ' ≤ ½` gives advantage at least `γ' − δ`; so advantage at most `γ` rules out
+  weak learning with `γ + δ < γ' ≤ ½` at confidence `δ`.
 * `PAC.predictSuccess_coin`: the learner that outputs its coin succeeds with probability exactly
   `½` (non-vacuity).
 
@@ -83,18 +85,21 @@ theorem trialDist_eq (m : ℕ) :
 
 /-- **The prediction game** [PS10, §8.1]: the probability that the learner `L`, given `m`
 uniform examples labelled by a uniform concept `C_i` and uniform coins, predicts the label of a
-fresh uniform point. -/
+fresh uniform point. [PS10] leaves the sample law and "a new sample" implicit. Here both are
+uniform and independent, so the fresh point may coincide with an example. -/
 noncomputable def predictSuccess (C : I → X → Bool) (m : ℕ)
     (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
   ((trialDist X I ρ m).prod (FinDist.uniform X)).probTrue
     fun w => L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2
 
-/-- The success probability as a probability over a trial and a fresh point. -/
+/-- The success probability is the probability, over a trial `(i, (s, r)) ← trialDist` and an
+independent uniform point `x`, of the event `L(s labelled by C_i, r)(x) = C_i(x)`. -/
 theorem predictSuccess_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
     predictSuccess C m L = ((trialDist X I ρ m).prod (FinDist.uniform X)).probTrue
       (fun w => L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2) := rfl
 
-/-- The **prediction advantage** `|Pr[correct] − ½|`. -/
+/-- The **prediction advantage** `|Pr[correct] − ½|` [PS10, §8.1, proof of Thm 179.1]: "better
+than `½ + ε`", read two-sidedly. An upper bound on it bounds the one-sided success. -/
 noncomputable def predictAdv (C : I → X → Bool) (m : ℕ)
     (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
   |predictSuccess C m L - 1 / 2|
@@ -110,7 +115,8 @@ noncomputable def expectedErr (C : I → X → Bool) (m : ℕ)
   (trialDist X I ρ m).expect
     fun t => err (FinDist.uniform X) (L (label (C t.1) t.2.1) t.2.2) (C t.1)
 
-/-- The expected error as an expectation over a trial. -/
+/-- The expected error is the expectation, over a trial `(i, (s, r)) ← trialDist`, of the
+uniform error `err_U(L(s labelled by C_i, r), C_i)`. -/
 theorem expectedErr_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
     expectedErr C m L = (trialDist X I ρ m).expect
       (fun t => err (FinDist.uniform X) (L (label (C t.1) t.2.1) t.2.2) (C t.1)) := rfl
@@ -182,7 +188,10 @@ theorem sub_le_predictAdv_of_weakLearnsUnder {C : I → X → Bool} {m : ℕ}
 
 /-- **Small prediction advantage rules out weak learning**: if the learner's prediction
 advantage is at most `γ`, it does not weakly learn the class under the uniform distribution with
-any `γ' ≤ ½` such that `γ + δ < γ'`, at confidence `δ`. -/
+any `γ' ≤ ½` such that `γ + δ < γ'`, at confidence `δ`. The confidence must be below the gap:
+at a constant confidence such as `δ = ½`, a learner with zero prediction advantage can satisfy
+`WeakLearnsUnder`. To refute weak learning in the sense of [KV94, §4.1], apply this at some
+`δ < γ' − γ`. -/
 theorem not_weakLearnsUnder_of_predictAdv_le {C : I → X → Bool} {m : ℕ}
     {L : (Fin m → X × Bool) → ρ → X → Bool} {γ γ' δ : ℝ} (hadv : predictAdv C m L ≤ γ)
     (hlt : γ + δ < γ') (hγ' : γ' ≤ 1 / 2) :

## ===== evidence-r2/checks.log =====

# lean_check_tree.sh at 6b781240bc438a103291c74b2ffefaa910f1a70d (maintainer re-check, 2026-11-05), in import order
TCSlib/InformationTheory/Samples rc=0 (no diagnostics)
TCSlib/LearningTheory/PAC/Defs rc=0 (no diagnostics)
TCSlib/LearningTheory/PAC/Prediction rc=0 (no diagnostics)
TCSlib/LearningTheory/PAC rc=0 (no diagnostics)

# style_lint.py: 0 findings in each of the four changed files

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
  Algorithms*, Cambridge University Press, 2014, §3.1 (the i.i.d. sample `S ~ D^m`).
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
`Pr[s] = ∏ j, p (s j)` ([SSBD14, §3.1], `S ~ D^m`). -/
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
- **Unrestricted parameters.** `ε`, `δ` and the weak-learning edge `γ` are arbitrary reals, where
  the sources take `ε, δ ∈ (0, 1)` ([KV94]: `(0, ½)`) and `γ > 0`. The docstrings of the
  predicates list the degenerate cases.
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
* `PAC.WeakLearnsUnder`, `PAC.WeakLearns`: weak learning at a fixed edge `γ`, accuracy `½ − γ`
  [KV94, §4.1].

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
  1994, §1.2 (PAC learning) and §4 (weak learning).
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

/-- **Weak learning under `D`** [KV94, §4.1], by the learner `L` at fixed `m`, `γ`, `δ`: PAC
learning under `D` with accuracy `½ − γ`, a hypothesis better than a fair coin by the edge `γ`.
[KV94] asks for this under every distribution, at an edge `γ = 1/p(n, size(c))`, and for every
confidence `δ`, in time polynomial in `1/δ`; here `D`, the real edge `γ` and the confidence `δ`
are fixed. Each relaxation makes the predicate weaker, so a refutation for a given learner is
stronger.

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

/-- **Weak learning** [KV94, §4.1], by the learner `L` at fixed `m`, `γ`, `δ`: under every
distribution `D` on `X`, PAC learning with accuracy `½ − γ` (`WeakLearnsUnder`). [KV94] takes
the edge `γ = 1/p(n, size(c))` and asks for every confidence `δ`, in time polynomial in `1/δ`;
here the real edge `γ` and the confidence `δ` are fixed. Each relaxation makes the predicate
weaker, so a refutation for a given learner is stronger.

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
confidence `δ` has expected error at most `ε + δ`, hence prediction success at least `1 − ε − δ`.
So a learner whose prediction advantage is at most `γ` cannot weakly learn under the uniform
distribution with `γ + δ < γ' ≤ ½` at confidence `δ` (`not_weakLearnsUnder_of_predictAdv_le`).
This is how layer 2 turns [PS10, Thm 179.1] into "no efficient learner weakly learns the class
under the uniform distribution" (for each learner, at a confidence below the edge).
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
* `PAC.sub_le_predictAdv_of_weakLearnsUnder`, `PAC.not_weakLearnsUnder_of_predictAdv_le`: weak
  learning with `γ' ≤ ½` gives advantage at least `γ' − δ`; so advantage at most `γ` rules out
  weak learning with `γ + δ < γ' ≤ ½` at confidence `δ`.
* `PAC.predictSuccess_coin`: the learner that outputs its coin succeeds with probability exactly
  `½` (non-vacuity).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1 (book p. 179).
* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994, §1.2 and §4.
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

/-- **Small prediction advantage rules out weak learning**: if the learner's prediction
advantage is at most `γ`, it does not weakly learn the class under the uniform distribution with
any `γ' ≤ ½` such that `γ + δ < γ'`, at confidence `δ`. The confidence must be below the gap:
at a constant confidence such as `δ = ½`, a learner with zero prediction advantage can satisfy
`WeakLearnsUnder`. To refute weak learning in the sense of [KV94, §4.1], apply this at some
`δ < γ' − γ`. -/
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
  a small prediction advantage rules out weak learning under the uniform distribution, for that
  learner, at confidence below the gap.

## References

* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994.
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

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
- **PAC learning:** `PACLearns C L m ε δ :=` for every `i` and every `D`, with probability
  `≥ 1 − δ` over the sample and the coins, `err D (L S r) (C i) ≤ ε`. Variants:
  - weak learning: `ε = ½ − γ` [KV94, §4];
  - learning under a fixed distribution: `D` fixed to uniform, the case [PS10] needs.
- **The prediction game (Def 179.a):** sample `i`, `m` examples and a fresh `x`, all uniform;
  the learner predicts `C i x`.
- **The bridge (proved here):** the prediction success equals `1 − E_{i,S,r}[err_U(L S r, C i)]`.
  The fresh point is independent of the sample, so no fresh-point collision issue arises. Hence
  a learner with prediction advantage `≤ γ` cannot weakly PAC-learn with any `γ' > γ`, at a
  stated `δ` (Markov on the error).

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
