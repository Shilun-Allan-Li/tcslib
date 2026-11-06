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
