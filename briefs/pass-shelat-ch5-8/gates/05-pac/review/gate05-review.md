# Gate 05 (Pass–shelat ch. 5–8, S3d layer 1, PAC learning): review of the external audit

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/05-pac/findings/gate05-pac-findings.md` (16 findings,
  F1–F16), against PR #194 at `44d27f39c233849a3a30a117bf15434610e485e9` (worktree `wt-pac`; HEAD
  verified). Also read: the pack, S3d §"Layer 1", `policy.md`, the evidence folder
  `briefs/pass-shelat-ch5-8/evidence/pac-2026-11-05/`, [PS10] p. 179 (`source-pdf/ch5-8.txt:1816–1837`),
  and prong D's consumer `TCSlib/Cryptography/Randomness/Learning.lean` (worktree `wt-prong-d2` at
  `c6198d86`). Prong D's copies of `Samples.lean`, `PAC/Defs.lean` and `PAC/Prediction.lean` are
  byte-identical to `44d27f39`.
- **Not available:** [KV94] and [SSBD14]. Claims about them are from memory and marked "(from memory)".
- **Not done:** no Lean build, as instructed. I re-derived A2, A4 and A5 by hand. A5 was also checked
  numerically (`gate03-review/scripts/a5_check.py`, run with `python3 -I`).

## Summary

- **F1 is true, and I agree it is a major.**
  - At a fixed `m`, `PACLearnable C m ε δ` and textbook learnability are incomparable.
  - A learnable class satisfies `PACLearnable C m ε δ` only from `m ≥ m_H(ε, δ)` on. So
    `¬ PACLearnable C m ε δ` is a lower bound on the sample size, not non-learnability. A2 checks this.
  - Over a finite `X`, every class satisfies `PACLearnable C m ε δ` for large `m` once `ε, δ > 0`.
    The learner that returns a consistent concept (ERM) does it. This includes the PRF class (A3).
  - The docstring also says [SSBD14, Def 3.1] needs a polynomial sample size. It does not.
  - The auditor missed one more instance of the same mix-up: `Prediction.lean:27–28` says the class
    is "not weakly learnable".
  - **I recommend removing `PACLearnable` and `pacLearnable_iff`** and rewriting the deviation as a
    statement about single learners. `PACLearnable` is not in S3d's list for layer 1, and nothing uses
    it. This needs your ruling (**Q1**).
  - The auditor's docstring-only fix would also clear the major, but its suggested text needs four
    corrections (listed under F1).
- **Verdicts.**
  - True: 11 (F1, F3, F5, F6, F8, F9, F10, F11, F12, F13, F16).
  - Partly true: 5 (F2, F4, F7, F14, F15).
  - False: none.
  - F16 (the auditor could not read p. 179) is resolved here from the source text.
- **Severities.**
  - I agree with every severity except F5. I propose moving F5 from minor to note: the Lean statement
    and its docstring are exact, and prong D already quantifies `δ` below the gap.
  - Once F1 is repaired, the gate stands at **0 blockers, 0 majors, 7 minors (F2, F3, F4, F6, F7, F8,
    F9), 8 notes (F5, F10–F16)**, so it can close.
- **Prong D's `Learning.lean` is not affected by any recommended fix.**
  - Thm 179.1 uses only `predictAdv`, `WeakLearnsUnder` and `not_weakLearnsUnder_of_predictAdv_le`,
    plus `main`'s `FinDist.uniform`. No recommended fix changes their statements.
  - Its part (c) assumes `δ < γ`, which is the form F5 asks for.
- **Rulings needed:** **Q1** (F1: what to do with `PACLearnable`) and **Q2** (F9: move `probTrue`
  now or later). Everything else is docstring work, or optional lemmas at the maintainer's discretion.
- **What the auditor missed (§3), in brief:**
  - The `Prediction.lean:27–28` sentence.
  - Three more `_eq` docstrings that break F8's rule.
  - `predictAdv` has no `[PS10]` tag.
  - The coin model compared with [SSBD14]'s deterministic learners.
  - F2's own overstatement.
  - CI never builds the root `TCSlib.lean` before merge.
  - The ch. 2–4 branch's parallel probability APIs, which need a ledger entry.
  - The specific bridge lemmas layer 2 will need.
  - An inventory remark that reads like a source requirement.

## 1. What prong D's Thm 179.1 uses

These are the uses in `wt-prong-d2/TCSlib/Cryptography/Randomness/Learning.lean` (`c6198d86`), found
by searching the whole branch:

| Declaration | Defined at `44d27f39` | Used at `Learning.lean` |
|---|---|---|
| `predictAdv` | `PAC/Prediction.lean:98` | `:94` (statement of (b)), `:116` |
| `WeakLearnsUnder` | `PAC/Defs.lean:158` | `:102` (statement of (c)) |
| `not_weakLearnsUnder_of_predictAdv_le` | `PAC/Prediction.lean:186` | `:118` (proof of (c)) |
| `FinDist.uniform` | `main`, `InformationTheory/FinDist.lean:83` | `:102` |

- **Reached through those definitions:** `predictSuccess`, `trialDist`, `label`, `PACLearnsUnder`,
  `accuracyProb`, `err`, `FinDist.iid`, `FinDist.expect`, `FinDist.probTrue`.
- **Used nowhere on the branch:** `PACLearnable`, `pacLearnable_iff`, `PACLearns`, `WeakLearns`,
  `pacLearns_const`, `not_pacLearnsUnder_of_neg`.
- **Consequence:**
  - No fix to `PACLearnable`, `PACLearns`, `WeakLearns`, or to any docstring, changes `Learning.lean`.
  - Only a change to the *statement* of `accuracyProb`, `PACLearnsUnder`, `predictSuccess` or
    `not_weakLearnsUnder_of_predictAdv_le` would reach it. That could happen through F4's
    generalisation, or through F12's sharpening if it replaced the existing lemma. I recommend
    neither.

## 2. The findings

### F1 (major): the "fixed parameters" deviation and `PACLearnable`

**Verdict: true.**

Evidence at `44d27f39`:
- `PAC/Defs.lean:27–31`: "`PACLearns C m L ε δ` fixes the sample size `m`, … The sources ask for one
  algorithm that works for all `ε, δ`, with a sample size polynomial in `1/ε`, `1/δ` … Here
  `PACLearnable C m ε δ` asks only for some learner at the given parameters. That notion is weaker, so
  impossibility results stated with it are stronger."
- `PAC/Defs.lean:177–181`: `PACLearnable`'s docstring reads "**PAC-learnability at fixed parameters**:
  some learner, with finite nonempty coins, learns `C` from `m` examples …". It has no `[Tag]` and no
  deviation note.

My check:
1. **The two notions are incomparable at a fixed `m`.**
   - [SSBD14, Def 3.1] (from memory, confident) says: there exist `m_H : (0,1)² → ℕ` and one
     deterministic algorithm `A` such that, for every `ε, δ ∈ (0,1)`, every `D` and every realizable
     labelling, `A` on `m ≥ m_H(ε, δ)` i.i.d. examples has error at most `ε` with probability at least
     `1 − δ`.
   - That gives `PACLearnable C m ε δ` (with `ρ' = Unit`) for every `m ≥ m_H(ε, δ)`, and nothing
     for smaller `m`.
   - In the other direction, one triple `(m, ε, δ)` says nothing about learnability.
   - So "weaker" is false. `¬ PACLearnable C m ε δ` says only that every learner with finite
     uniform coins needs more than `m` examples at `(ε, δ)`.
2. **A2 holds.** Take `X = Bool`, the four concepts, `m = 0`, uniform `D`, `ε = ¼`, `δ = ½`.
   - `Fin 0 → X × Bool` is a singleton, so `label c s` does not depend on `c`. The hypothesis
     therefore depends only on the coin.
   - Under uniform `D`, `err ∈ {0, ½, 1}`, so `err ≤ ¼` holds exactly when `h = c`.
   - Summed over the four targets, `accuracyProb = Σ_c Pr_r[h_r = c] ≤ 1`. So some target has accuracy
     at most `¼ < ½`, and `¬ PACLearnable C 0 ¼ ½`.
   - Yet the class is finite, so it is learnable.
   - The union bound over the three non-target concepts gives `3(¾)^m ≤ ½` from `m = 7` on. The
     auditor's 8 and 9 are also valid, just not tight; this does not matter.
3. **The strong reading never holds in range.** Over a finite `X`, the range of `C` has at most
   `2^|X|` members.
   - Let ERM output any concept of the class consistent with its sample (`ρ' = Unit`). It fails only
     if some concept with error greater than `ε` is consistent with all `m` examples.
   - That has probability at most `2^|X| (1 − ε)^m ≤ δ` once `m ≥ (|X| ln 2 + ln(1/δ))/ε`.
   - So for `ε, δ > 0`, `∃ m, PACLearnable C m ε δ` holds for every class.
   - At `ε = 0` it can fail: put a tiny mass on a point where two concepts differ, and no fixed `m`
     is enough.
4. **A3 holds.** The PRF class has at most `2^n` concepts, so `m = ⌈(n ln 2 + ln(1/δ))/ε⌉` works.
   A layer-2 statement "`¬ PACLearnable`" would be false. The hardness is computational.
5. **The description of the sources is wrong.**
   - [SSBD14]'s `m_H` is an arbitrary function. No polynomial bound is required.
   - Polynomial bounds come from [KV94]'s efficiency requirement (from memory): running time
     polynomial in `1/ε`, `1/δ`, and from §1.2.2 also in `n` and `size(c)`. The running time bounds
     the number of examples.
6. **Statements about a single learner are not affected.**
   - A source learner run on its own `m ≥ m_H(ε, δ)` examples is one `L` with `PACLearns C m L ε δ`.
   - So a statement that refutes `PACLearns` or `WeakLearnsUnder` for every learner of a class of
     algorithms is faithful. Prong D's Thm 179.1(c) is of this kind: it covers every NUPPT and every
     polynomial `m`.
   - The defect is only the existential `PACLearnable` and the prose comparing it with learnability
     of the class.

**Severity: agree, major.**
- The trusted prose makes a false claim about the logical strength of an exported predicate.
- The predicate's textbook name invites exactly the misuse that A3 refutes.
- No Lean statement is wrong, and nothing uses `PACLearnable`, so it is not a blocker.

**Fix options.** All four are described in **Q1** (§4). The recommended one is (a): remove
`PACLearnable` and `pacLearnable_iff`, and rewrite the prose as follows.

- `PAC/Defs.lean:26–32`, the module's deviation bullet, replaced by:
  ```
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
  ```
- `PAC/Defs.lean:144–147` (`PACLearns`), replaced by: "**A PAC learner at fixed parameters**
  [KV94, §1.2.1], [SSBD14, Def 3.1]: … under `D`. The sources require this of one algorithm for every
  `ε, δ` and every large enough `m`. Here `m`, `ε`, `δ` are fixed, unrestricted reals (module
  deviations)."
- `PAC/Defs.lean:45` (the `PACLearnable` line of "Main definitions"): delete it.
- `PAC.lean:21–22`: change to "… PAC, weak and fixed-distribution learning, for a given learner at
  fixed parameters."
- `PAC/Prediction.lean:27–28`: change to "This is how layer 2 turns [PS10, Thm 179.1] into 'no
  efficient learner weakly learns the class under the uniform distribution' (for each learner, at a
  confidence below the edge). Information-theoretically the class is learnable; the hardness is
  computational." This sentence was missed by the auditor (§3, M1).

If option (c) is chosen instead (the auditor's docstring-only fix), its suggested text needs four
corrections:
1. "for all `ε, δ ∈ (0,1)`": [KV94] uses `(0, ½)` (from memory).
2. "Over a finite `X` every class is `PACLearnable` for large `m`": add "for `ε, δ > 0`" (see check 3).
3. "`¬ PACLearnable C m ε δ` says `m_H(ε, δ) > m`": `m_H` is any valid function, so this should say
   "every learner needs more than `m` examples at `(ε, δ)`".
4. "because extra examples can be ignored": this is needed only for [KV94]-style learners that draw a
   variable number of examples, since [SSBD14]'s `A` works for every `m ≥ m_H` directly. The
   monotonicity in `m` it relies on is not proved in the PR. Proving it needs a lemma on the marginal
   of `iid`, which is missing (F13). The prose should not refer to that lemma as if it existed.

**Prong D:** not affected under any of the options (§1).

**User ruling:** yes, Q1.

### F2 (minor): degenerate parameter ranges

**Verdict: partly true.**
- **Correct parts.** The parameters are unrestricted reals. The degenerate cases are not declared on
  `PACLearnsUnder` (`Defs.lean:133–134`) or `WeakLearnsUnder` (`:156–157`). The only witness that the
  predicate can fail, `not_pacLearnsUnder_of_neg`, uses `ε < 0`, outside every source's range, yet its
  docstring concludes "`PACLearns` is therefore not trivially satisfied" (`:208–210`; the module repeats
  it at `:53–54`).
- **One overstatement.** The auditor says the predicates hold "for every learner, at every parameter
  value" when `ε ≥ 1`. In fact `ε ≥ 1` makes `accuracyProb = 1`, so the predicate holds only if
  `δ ≥ 0`; at `δ < 0` it is false. The same applies to `γ ≤ −½`. The auditor's own A1 row states this
  correctly.

**Severity: agree, minor.**

**Fix (docstrings, plus an optional new theorem):**
- On `PACLearnsUnder`, `PACLearns` and `WeakLearnsUnder`, add: "The parameters are unrestricted reals;
  the sources take `ε, δ ∈ (0,1)` ([KV94]: `(0, ½)`). Outside that range the predicate is degenerate:
  every learner satisfies it when `δ ≥ 1`, when `ε ≥ 1` and `δ ≥ 0`, or when `I` is empty; no learner
  satisfies it when `I` is nonempty and `ε < 0` or `δ < 0`. For weak learning only `γ > 0` is weak
  learning, and `γ ≤ −½` (with `δ ≥ 0`) is trivial."
- Reword `not_pacLearnsUnder_of_neg`'s last sentence to: "So `PACLearnsUnder` fails at every negative
  accuracy (a witness outside the sources' range)." Fix the module line `:53–54` the same way.
- Optionally, add a witness inside the range. A smaller one than the auditor's A2:
  ```lean
  /-- **With no examples, no learner tells two concepts apart** (non-vacuity in range): on a
  one-point domain with the two constant concepts, every learner with `m = 0` fails at every
  accuracy `ε < 1` and confidence `δ < ½`.

  **Proof sketch.** With no examples the hypothesis depends on the coins only. Its error against
  the constant `b` is `0` when it outputs `b` and `1` otherwise, so the two accuracy probabilities
  sum to at most `1 < 2(1 − δ)`. -/
  theorem not_pacLearnsUnder_const_pair (D : FinDist Unit)
      (L : (Fin 0 → Unit × Bool) → ρ → Unit → Bool) {ε δ : ℝ} (hε : ε < 1) (hδ : δ < 1 / 2) :
      ¬ PACLearnsUnder D (fun (b : Bool) (_ : Unit) => b) 0 L ε δ
  ```
  The range `δ < ½` falls inside [KV94]'s. The proof should take roughly 30–50 lines. This is new
  API, so the auditor must check it in the closing round.

**Prong D:** not affected.

**User ruling:** no. The optional theorem is the maintainer's choice; I recommend adding it.

### F3 (minor): improper learning is not declared

**Verdict: true.**
- The learner may output any `X → Bool` (`Defs.lean:22–23`, `:148`).
- [KV94]'s preliminary definition, §1.2.1, requires `h ∈ C` (from memory). "PAC learnable using `H`"
  comes later in [KV94].
- [SSBD14, Def 3.1] does not require `h ∈ H`.
- The module's deviations (`:26–34`) do not mention this.

**Severity: agree, minor.** For impossibility results, allowing any hypothesis is the stronger choice.
It still has to be declared.

**Fix (docstring):** add this bullet to the deviations: "**Improper hypotheses.** A learner may output
any `X → Bool` (representation-independent learning). [KV94, §1.2.1] requires `h ∈ C`; [SSBD14,
Def 3.1] does not. A refutation is stronger without the restriction."

**Prong D:** not affected. `learnerOf`'s hypothesis is improper, and that is the right model.

**User ruling:** no.

### F4 (minor): the coin model

**Verdict: partly true.**
- **Incorrect part.** The auditor says the coin model "is not declared", but it is:
  - `Defs.lean:15`: "(learners are arbitrary functions, with finite random coins)";
  - `Defs.lean:22–23`: "its coins are uniform on the finite type `ρ`";
  - `Defs.lean:119–121`, on `accuracyProb`: "and uniform coins".
- **Correct part.** What is not declared is how this model compares with general randomized learners.
  A5 is correct: I re-derived it by hand.
  - Let `q` be the probability that the learner outputs `c₂` on the example `(a,0)`. Meeting
    `δ = 1/3` for all three concepts forces `q = 1/(3p) = 1/√3`, which is irrational.
  - `scripts/a5_check.py` confirms this. The real optimum is exactly `2/3`. The best finite uniform
    coin space with at most 200 points reaches 0.666642.
- **Context the auditor omits.** Uniform coins on a finite type are exactly the model of a fair-coin
  algorithm with bounded running time. That covers [KV94]'s randomized learners, with polynomial
  time, and [SSBD14]'s deterministic ones, which are the case `ρ = Unit`. The gap A5 exhibits is
  against learners that mix with arbitrary real probabilities, which neither source uses for
  efficient learning.

**Severity: agree, minor.** If Q1(a) is adopted, I would accept a note: no statement of the form
"`∃` a learner" then remains in layer 1. The gap only matters for statements of the form
`¬ ∃ ρ L, …` at a fixed `D` and exact thresholds.

**Fix (docstring, recommended).** Add this bullet: "**Coins.** A learner's coins are uniform on a
finite type: every fair-coin algorithm with bounded running time ([KV94]); [SSBD14]'s deterministic
learners are `ρ = Unit`. A learner that needs an irrational mixing probability is not of this form. At
a fixed `D` and an exactly tight `δ` this can matter, so a statement `¬ ∃ ρ L, …` rules out fair-coin
learners, not every randomized learner."

**Not recommended:** generalizing the coins to `μ : FinDist ρ`. That would change the statements of
`accuracyProb`, `trialDist` and `predictSuccess`, and with them prong D's (b) and (c).

**Prong D:** not affected by the docstring fix. The generalization would affect it.

**User ruling:** none for the docstring fix. The generalization would need one; I do not propose it.

### F5 (minor; proposed: note): `not_weakLearnsUnder_of_predictAdv_le` refutes only at `δ < γ' − γ`

**Verdict: true as an observation.**
- A4 holds. With `X = {a}`, the two constant concepts and `m = 1`, a learner that flips the label on
  coin `true` has `predictAdv = 0`. Yet it satisfies `WeakLearnsUnder U C 1 L γ' ½` for every
  `γ' ≤ ½`, because its accuracy is `½` whenever `ε = ½ − γ' ∈ [0, 1)`.
- So with constant confidence the bridge says nothing, and this cannot be improved.
- But the Lean statement and its docstring already state the condition exactly. `Prediction.lean:183–188`
  says "with any `γ' ≤ ½` such that `γ + δ < γ'`, at confidence `δ`". The module docstring
  (`:26–27`) says the same.
- The stale text is in the design note, S3d lines 47–49: "cannot weakly PAC-learn with any
  `γ' > γ`, at a stated `δ` (Markov on the error)". Both "any `γ' > γ`" and "Markov" are wrong, as F11
  also says.

**Severity: I propose note instead of minor.**
- The Lean surface is exact.
- The only consumer quantifies `δ` correctly. `Learning.lean:100–103` assumes `δ < γ ≤ ½` with both
  constants, and since the advantage tends to 0, `δ` sits below the gap from some `n` on.
- That refutes [KV94, §4.1]-style weak learning (from memory: such a learner must reach every `δ`, so
  in particular one below the edge).
- The change does not affect closure.

**Fix:**
- Optionally, add the auditor's sentence to the docstring of `not_weakLearnsUnder_of_predictAdv_le`:
  "The confidence must be below the gap; at constant confidence (for example `δ = ½`) a learner with
  zero advantage can weakly learn. To refute weak learning in the sense of [KV94, §4.1], apply this at
  some `δ < γ' − γ`."
- In the records, change S3d's sentence to "with `γ' > γ + δ` at confidence `δ` (the error is at most
  `ε` on the good event and at most 1 elsewhere)".

**Prong D:** not affected. Its (c) already has the right form. Its docstring at `:97–98` calls `δ` an
"edge", although `δ` is the confidence. That is for prong D's own gate (§3, M9).

**User ruling:** no.

### F6 (minor): attribution and deviations of the variants

**Verdict: true.**
- `PACLearnsUnder` (`Defs.lean:133–134`) has no `[Tag, location]`.
- `WeakLearnsUnder` and `WeakLearns` (`:156`, `:167`) cite "[KV94, §4]", which is a chapter. Weak
  learning is defined in §4.1 (from memory).
- The undeclared differences from [KV94], all from memory: [KV94] is distribution-free; its edge is
  `γ = 1/p(n, size(c)) > 0`, while here `γ` is any real; and its `δ` is an input that every value of
  must work for, while here `δ` is fixed.
- Each of these relaxations makes the predicate for a single learner weaker, so refuting it is
  stronger. Unlike F1, this argument is correct, because the statements are about a single learner.

**Severity: agree, minor.**

**Fix (docstrings):**
- `PACLearnsUnder`: "the fixed-distribution variant of [KV94, §1.2.1] / [SSBD14, Def 3.1] (the case
  [PS10, §8.1] needs); weaker than distribution-free learning."
- `WeakLearnsUnder` and `WeakLearns`: cite `[KV94, §4.1]`, and add: "at a fixed real edge `γ` (weak
  learning when `γ > 0`; [KV94] takes `γ = 1/p(n, size(c))`) and a fixed confidence `δ` ([KV94] asks
  for every `δ`, in time polynomial in `1/δ`). Each relaxation makes the predicate weaker, so a
  refutation for a given learner is stronger."
- Fix the module "Main definitions" line `:44` the same way.

**Prong D:** not affected.

**User ruling:** no.

### F7 (minor): the readings of [PS10] are declared only at module level

**Verdict: partly true.**
- **What is already on the declaration.** `predictSuccess`'s own docstring (`Prediction.lean:84–86`)
  already gives the uniform reading: "given `m` uniform examples labelled by a uniform concept `C_i` and
  uniform coins, predicts the label of a fresh uniform point".
- **What is only in the module's "Source notes" (`:30–32`):**
  - that this is a *reading*, because the source leaves the distribution implicit;
  - that the fresh point is independent, and so may coincide with an example ("fresh" alone could be
    read as "unseen");
  - that the advantage is read two-sided.
- `predictAdv` (`:97`) has no source tag at all (§3, M3).

**Severity: agree, minor.**

**Fix (docstrings):**
- `predictSuccess`, add: "[PS10] leaves the sample law and 'a new sample' implicit. Here both are
  uniform and independent, so the fresh point may coincide with an example."
- `predictAdv`, add: "[PS10, §8.1, proof of Thm 179.1]: 'better than `½ + ε`', read two-sidedly. An
  upper bound on it bounds the one-sided success."

**Prong D:** not affected. Prong D's (b) is stated two-sidedly. That is stronger than the source's
one-sided claim, and still true for a PRF, because flipping a learner's output is again a NUPPT.

**User ruling:** no.

### F8 (minor): the `_iff` docstrings are bare labels

**Verdict: true.** `Defs.lean:139, 152, 162, 172, 184` are of the form "`X` unfolded." Policy §1 says
"each docstring states its formula", and §2 says "A bare label … is not a statement". The lint checks
only that a docstring is present.

**Severity: agree, minor.** The rule also catches three `_eq` docstrings that the auditor did not list
(§3, M2).

**Fix (docstrings):**
- For example: "`PACLearnsUnder D C m L ε δ` holds iff `1 − δ ≤ accuracyProb D (C i) m L ε` for every
  `i`."
- If Q1(b) or (c) is chosen, `pacLearnable_iff` needs the same treatment. Under Q1(a) it is deleted.

**Prong D:** not affected.

**User ruling:** no.

### F9 (minor): `Samples.lean` imports `Extractors` to get `probTrue`

**Verdict: true.**
- `Samples.lean:5` is `import TCSlib.InformationTheory.Extractors`.
- `FinDist.probTrue` and `probTrue_eq` are defined at `Extractors.lean:62` and `:78`.
- `Extractors` imports `Entropy` and `LeftoverHash`.
- `Samples.lean` and the PAC files use nothing else from that closure.
- On `main` plus the PR, `probTrue` is used only by `Extractors`, `Samples` and the two PAC files.
- S3d says that layer 1 "depends on `main`'s `FinDist` only". Its import closure is wider.

**Severity: agree, minor.**

**Fix (moves code, no statement change):**
- Move `FinDist.probTrue` and `FinDist.probTrue_eq`, verbatim and with the same full names, into
  `FinDist.lean`.
- `Samples.lean` then imports `TCSlib.InformationTheory.FinDist`. It may also need a Mathlib import
  for `Finset.prod_univ_sum` or `Fintype.piFinset_univ`; elaboration will show.
- `Extractors.lean`'s "Main definitions" list drops `probTrue`.
- Downstream code needs no edits.

**Prong D:** not affected. The names are unchanged. `Learning.lean` uses nothing that reaches it only
through `Extractors`.

**User ruling:** yes, **Q2**, because doing it now touches two files on `main` that passed gate 01.

### F10 (note): no duplication

**Verdict: true for `main`.** At `7d36bbc` I find:
- no `expect`, `iid`, `probTrue_not` or `probTrue_true` on `FinDist`;
- `BooleanAnalysis`'s expectations (`Basic.lean:86`, `Hypercontractivity/Products/Basic.lean:161`),
  which live on other carriers.

The auditor missed the ch. 2–4 branch, where layer 2 lives (§3, M5).

**Severity: agree, note.**

**Fix:** none in the PR. Add a "not a copy" row to the ledger (M5).

**Prong D:** not affected.

**User ruling:** no.

### F11 (note): `expect_le_add_of_le_one`

**Verdict: true.**
- Both hypotheses are necessary. With `f ≡ 1` and `ε = −1` the conclusion reads `1 ≤ 0`; with
  `f ≡ 2` and `ε = 0` it reads `2 ≤ 1`.
- No lower bound on `f` is used. So "`[0, 1]`-valued" (`Samples.lean:31`, `:113`) understates the
  theorem.
- The step goes from a tail bound to an expectation. That is not Markov's inequality, which goes the
  other way.

**Severity: agree, note.**

**Fix (optional docstring):** say "with values at most 1". Fix S3d's "Markov" in the records.

**Prong D:** not affected.

**User ruling:** no.

### F12 (note): the bound has slack, and the module omits `ε ≥ 0`

**Verdict: true.**
1. **The bound can be sharpened.** On the good event the error is at most `ε`, and elsewhere at
   most 1. So `E[err] ≤ ε(1 − q) + q = ε + (1 − ε)q ≤ ε + (1 − ε)δ`, where `q ≤ δ` is the probability
   of the bad event.
   - This gives an advantage of at least `γ' − δ(½ + γ')`.
   - At `γ' = ½` it equals the existing bound, which A4 shows is tight there.
2. **A one-sided hypothesis suffices.**
3. **The module omits `ε ≥ 0`.**
   - `Prediction.lean:25` says "has expected error at most `ε + δ`", and `:44–46` likewise, without
     `ε ≥ 0`. `:47–49` also omits `γ ≤ ½`.
   - Counterexample: a single concept `c`, a learner that outputs `¬c`, `ε = −1`, `δ = 1`. Then
     `PACLearnsUnder` holds but `E[err] = 1 > 0`.

**Severity: agree, note.**

**Fix:**
- Add "for `ε ≥ 0`" and "for `γ ≤ ½`" to the module docstring.
- If the sharper bound is wanted, add it as *new* lemmas. Do not change the existing statements, which
  prong D calls.

**Prong D:** not affected, provided the existing lemmas are kept.

**User ruling:** no.

### F13 (note): no decomposition lemmas for `iid`

**Verdict: true.** `FinDist.iid` comes only with `iid_apply` (`Samples.lean:148`).

**Severity: agree, note.**

**Fix:** add the lemmas with layer 2, not now. To make it specific, prong D's proof of (b) will
probably need:
- `FinDist.iid_uniform : (uniform α).iid m = uniform (Fin m → α)`;
- `FinDist.prod_uniform : (uniform α).prod (uniform β) = uniform (α × β)`;
- on the ch. 2–4 side, a bridge from `(uniform α).probTrue D` to `uprob`.

These would turn `predictSuccess` into a uniform probability over keys, points and coins, which is the
form the PRF game is stated in. Each lemma is short. Monotonicity in `m` (Q1(b)) would need the
marginal lemma.

**Prong D:** its proof of (b), currently a `sorry`, is the consumer.

**User ruling:** no.

### F14 (note): the `iid` citation and an unused reference

**Verdict: partly true.**
- **True:** `[Vad12, §6.1]` appears in `Samples.lean`'s References (`:38`), but no declaration in the
  file cites it.
- **Defensible as it stands:** the citation `[SSBD14, §3.1]` for `S ~ D^m` (`:37`, `:136`). Def 3.1 is
  in §3.1 and uses `m` i.i.d. examples.
- **Probably the better location:** the i.i.d. assumption and the notation `S ∼ D^m` are introduced in
  §2.3.1 (from memory, fairly confident).

**Severity: agree, note.**

**Fix (docstring):**
- Cite "[SSBD14, §2.3.1] (the i.i.d. assumption, `S ∼ D^m`), as used in Def 3.1", once someone with
  the book confirms the location.
- Drop `[Vad12]` from `Samples.lean`'s References.

**Prong D:** not affected.

**User ruling:** no. The location needs someone with the book.

### F15 (note): "five modules" against six changed files

**Verdict: partly true.** The pack's wording is ambiguous, but the evidence answers the question.
- `evidence/pac-2026-11-05/replay.log` names the five modules: `Samples`, the `InformationTheory`
  facade, `PAC/Defs`, `PAC/Prediction` and the `PAC` facade.
- The README says the root `TCSlib.lean` "was not built, since its closure is the whole library", and
  reports a search for name clashes.
- The auditor had only the bundle, not the evidence.

**New point (§3, M6):**
- CI (`.github/workflows/push.yml`) runs only on pushes to `main`.
- No check runs exist at `44d27f39` (REST query: 0 runs, 0 statuses).
- So nothing builds the root before merge.
- I repeated the clash search on `main`: no other file declares the new full names (the `FinDist`
  namespace in `Entropy.lean` has no `expect`, `iid` or `probTrue_*`). The risk is low.

**Severity: agree, note.**

**Fix (records):**
- Name the five modules in the pack's attestation.
- Record that the root is first built by CI after merge, or build `TCSlib.lean` once before merging.

**Prong D:** not affected.

**User ruling:** no.

### F16 (note): the wording of p. 179 was not checked

**Verdict: true as a limitation of the audit, and now resolved.** `ch5-8.txt:1817–1837` reads:
> "The Learning Question: For a random `i ∈ I`, given samples `(x_j, b_j)` such that `x_j ∈ S` and
> `b_j = 1` iff `x_j ∈ C_i`, determine for a bit string `x` if `x ∈ C_i`." … "No (n.u.) p.p.t. can
> predict whether a new sample `x` is in `C_i` better than `½ + e`."

How this bears on the formal reading:
- The source gives no distribution for the samples.
- "A new sample" means a further sample. Nothing requires `x ∉ {x_j}`.
- "For a random `i`" fits a uniform index, since `I = {0,1}^n` in the sketch.
- "Better than `½ + e`" is one-sided.

So the formal reading is compatible with the text: uniform, independent, the fresh point may coincide
with an example, and the advantage is two-sided (a strengthening; see F7). It remains a reading and
should be declared as one (F7).

**Severity: note.** Nothing further is needed for the gate.

**Fix:** none in the code. One records fix: the inventory row for Thm 179.1
(`inventory-ch5-8.md:139`) says "A fresh point must avoid the sampled ones" (§3, M8).

**Prong D:** not affected.

**User ruling:** no.

## 3. What the auditor missed

- **M1 (part of F1's repair).** `Prediction.lean:27–28`: "This is how layer 2 turns [PS10, Thm 179.1]
  into 'the class is not weakly learnable'."
  - This is the same mix-up of a statement about the class with statements about single learners.
  - Information-theoretically the PRF class *is* weakly learnable, by ERM (A3).
  - The repair text is under F1.
  - Related: `PAC.lean:23–24` says "a small prediction advantage rules out weak learning" without the
    condition on `δ`. Add "for that learner, at confidence below the gap".
- **M2 (part of F8).** Three docstrings describe their formula without stating it:
  - `accuracyProb_eq` (`Defs.lean:127`): "… as a probability over the examples and the coins";
  - `predictSuccess_eq` (`Prediction.lean:92`);
  - `expectedErr_eq` (`:113`).

  Each should state its event or integrand.
- **M3 (part of F7).** `predictAdv` (`Prediction.lean:97`) is the source's "better than `½ + ε`"
  quantity, but it carries no `[PS10, …]` tag.
- **M4 (part of F4).**
  - [SSBD14, Def 3.1]'s learner is deterministic: the probability is over the examples only (from
    memory). Here learners are randomized. Neither the coin model nor F4 mentions this.
  - The finite uniform model is exactly [KV94]'s fair-coin, bounded-time model, and it contains
    [SSBD14]'s learners as the case `ρ = Unit`. The bullet proposed under F4 covers this.
  - Also in F2, the auditor's "ε ≥ 1 … at every parameter value" needs `δ ≥ 0`.
  - Also in F1, the auditor's suggested replacement text needs the four corrections listed there.
- **M5 (ledger).** On the ch. 2–4 branch, where layer 2 lives, there are parallel probability APIs on
  other carriers:
  - `Foundations/Probability.lean`: `uexp` and `uprob`, with `uprob_not`, `uprob_true`, `uprob_prod`
    and `uprob_or_le`;
  - `Games/Probability.lean`: `ProbComp.expect` and `prob`, with linearity, `prob_not`, and
    `dist : ProbComp α → FinDist α`.

  They are not copies. But `(uniform α).expect f = uexp f` and `uniform_probTrue ≈ uprob` will be
  needed when the branches meet. The campaign records such cases as "not a copy (different carriers)"
  rows (DL-4, DL-5), so I propose a **DL-9** row:

  | DL-9 | Not a copy (different carriers): `FinDist.expect`, `probTrue_not`, `probTrue_true`, `expect_prod` (#194, `InformationTheory/Samples.lean`, for `main`) and `uexp`/`uprob`, `uprob_not`, `uprob_true`, `uprob_prod` (`Foundations/Probability.lean`) and `ProbComp.expect`/`prob_not` (`Games/Probability.lean`), on the ch. 2–4 branch | proposed | Bridge lemmas when layer 2's proof of (b) needs them, or when ch. 2–4 lands on `main`. |

  This needs the user's acknowledgement, as every ledger entry does. It does not block gate 05.
- **M6 (part of F15).** Nothing builds the root before merge, because CI runs only on pushes to
  `main` (see F15).
- **M7 (part of F13).** The bridge lemmas layer 2 will need are listed under F13.
- **M8 (records).** The inventory's remark on Thm 179.1 says "A fresh point must avoid the sampled
  ones" (`inventory-ch5-8.md:139`).
  - That is not in the source (F16).
  - It is the collision event that the proof charges (S3d, layer 2, step 2), and it could be misread
    as part of the definition.
  - Reword it to: "the proof charges the event that the fresh point was among the samples".
- **M9 (downstream, prong D's own gate; not gate 05).** Two points in `Learning.lean`:
  - Its (c) docstring (`:97–99`) calls `δ` an "edge". It should say "confidence `δ` below the edge
    `γ`".
  - (c) is stated for constant `γ` and `δ` only. The layer-1 bridge also supports a noticeable
    `γ(n)` with `δ(n) ≤ γ(n)/2`, which is closer to [KV94]'s `γ = 1/p(n)`. Adopting that is prong D's
    choice.
- **M10 (records).** S3d line 40 writes `PACLearns C L m ε δ`, but the code's argument order is
  `C m L ε δ`. Fix this together with F5's sentence and F11's "Markov".

## 4. Questions for the user

**Q1 (F1). What should layer 1 do with `PACLearnable C m ε δ`, the predicate "some learner works at
these fixed parameters"?**

- **(a) Remove `PACLearnable` and `pacLearnable_iff`, and rewrite the deviation as a statement about
  single learners (recommended).**
  - Keep `PACLearns`, `PACLearnsUnder` and `WeakLearns(Under)`.
  - Rewrite the "Fixed parameters" bullet, `PACLearns`'s docstring, the `PAC.lean` contents line and
    `Prediction.lean:27–28` (text under F1).
  - Cost:
    - the PR loses one definition and one theorem (14 → 13 definitions, 38 → 37 theorems);
    - elaboration, the axiom printout and the lint must be rerun on the three files and the facade;
    - the auditor confirms the rewrite in the closing round.
  - S3d's list for layer 1 never included `PACLearnable`, and nothing uses it.
  - Prong D is unaffected.
- **(b) Keep it as a statement about sample size, renamed `PACLearnableAt`, with rewritten
  docstrings.**
  - The docstring would say: "bounds the sample complexity; a learnable class satisfies it for every
    `m ≥ m_H(ε, δ)`; over a finite `X` every class satisfies it once `ε, δ > 0`; it cannot express
    computational hardness."
  - Optionally, prove `PACLearnableAt.mono` (more examples never hurt).
  - Cost:
    - the rename and the docstrings are cheap now;
    - the monotonicity lemma needs the marginal lemma for `iid` (F13), roughly 60–120 lines;
    - an unused trusted declaration stays in the library.
- **(c) Docstring-only, keeping the name (the auditor's fix, with the four corrections under F1).**
  - Cost: smallest.
  - But the textbook name stays. A blind restatement or a later consumer may still read it as
    [SSBD14, Def 3.1], and `¬ PACLearnable` for Thm 179.1 would be a false statement (A3).
- **(d) Also add the textbook notion: one algorithm, with a sample function `m_H(ε, δ)`.**
  - Not recommended.
  - Over a finite `X` it holds for every class (ERM), so it fails the pack's trivialization check.
  - A meaningful version needs a family `X_n = {0,1}^n` with a polynomial sample bound. The PRF class
    satisfies that too (A3), so it still says nothing about Thm 179.1.
  - Cost:
    - new definitions;
    - the ERM theorem, which needs a union bound over `iid` and F13's lemmas;
    - a new gate round.

**Q2 (F9). `Samples.lean` imports `Extractors`, and so the leftover hash lemma, only to get
`FinDist.probTrue`. When should `probTrue` move into `FinDist.lean`?**

- **(a) Later: record it in the queue, and move it in a small follow-up PR to `main` (recommended).**
  - Cost: one queue entry now, and a short PR later.
  - The full names do not change, so nothing written against #194 in the meantime has to change.
- **(b) Now, in #194, as a separate commit that only moves code.**
  - Cost: the PR's diff grows into `FinDist.lean` and `Extractors.lean`, two files that passed
    gate 01.
  - Every `InformationTheory` module must be re-elaborated.
  - The auditor must check that the move is verbatim.

## 5. Edits to close the gate, on the recommended path (Q1(a), Q2(a))

1. **`PAC/Defs.lean`**
   - Delete `PACLearnable` and `pacLearnable_iff` (`:176–188`) and the "Main definitions" line `:45`.
   - Rewrite the deviation bullets at `:26–34` (F1). Add the bullets for improper hypotheses (F3) and
     coins (F4).
   - Docstrings:
     - `PACLearnsUnder`: tag and parameter ranges (F6, F2).
     - `PACLearns`: F1 and F2.
     - `WeakLearns(Under)`: `[KV94, §4.1]`, the deviations and the parameter ranges (F6, F2).
     - The four remaining `_iff` lemmas and `accuracyProb_eq`: state the formulas (F8, M2).
     - `not_pacLearnsUnder_of_neg` and the module line `:53–54`: F2.
   - Optionally, add `not_pacLearnsUnder_const_pair` (F2).
2. **`PAC/Prediction.lean`**
   - Fix the module sentence at `:27–28` (F1, M1).
   - Add "for `ε ≥ 0`" and "for `γ ≤ ½`" at `:25` and `:44–49` (F12).
   - Docstrings on `predictSuccess` and `predictAdv`: the readings and a tag (F7, M3).
   - `predictSuccess_eq` and `expectedErr_eq`: state the formulas (M2).
   - Optionally, the sentence on `not_weakLearnsUnder_of_predictAdv_le` (F5).
3. **`PAC.lean`:** update the contents lines `:21–24` (F1, M1).
4. **`Samples.lean`:** "values at most 1" (F11). Remove `[Vad12]` from the References (F14). Move the
   §2.3.1 citation only once someone with the book confirms it.
5. **Records (no code)**
   - Queue entry for F9 (Q2(a)). DL-9 row (M5), for the user's acknowledgement.
   - S3d: F5's sentence, F11's "Markov", M10's argument order.
   - Inventory row 139 (M8).
   - Pack attestation: name the five modules, and say how the root gets built (F15, M6).
6. **Re-attest:** elaboration of the five modules, axioms (37 theorems, or 38 with the optional
   witness), and the lint.
7. **Closing round:** the auditor confirms F1 is closed and checks any new theorem.
8. **Prong D:** no edit. M9 is for its own gate.
