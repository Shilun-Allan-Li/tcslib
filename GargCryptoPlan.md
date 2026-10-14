# Garg, *A Course in Theory of Cryptography*, Chapters 1–3

## Objective and source

Formalize Chapters 1–3 of [Gar26] S. Garg, *A Course in Theory of Cryptography*, UC
Berkeley lecture notes, draft of 22 January 2026: negligible functions, one-way
functions (robustness, brittleness, Yao amplification, Levin's universal one-way
function, hard-concentrate bits and Goldreich–Levin), and pseudorandomness
(statistical and computational indistinguishability, hybrid arguments, PRG
extension, PRGs from one-way permutations, GGM pseudorandom functions).

## Foundation decisions

1. **Two layers.** Every reduction is stated first in a *concrete layer*: one fixed
   value of the security parameter, adversaries are arbitrary functions of their input
   and a uniformly random coin string from a finite type, the reduction `B` is an
   explicit Lean function built from `A`, and the theorem is an exact inequality between
   success probabilities or advantages. The *asymptotic layer* (Phase B) adds
   non-uniform PPT machines, negligible functions and the closure facts that make `B`
   efficient when `A` is; the textbook statements are derived there.
2. **Probability** is uniform probability on finite types (`uprob`, `uexp` in
   `Foundations/Probability.lean`): exact counts. Non-uniform distributions are
   pushforwards of uniform seeds (samplers `σ → γ`). `InformationTheory/FinDist` and
   `statDist` are reused for statistical distance.
3. **Negligible** (`Foundations/Negligible.lean`) is defined on `ℕ → ℝ` with `|μ n|`,
   agreeing with [Gar26, Definition 1.4] on `[0, 1]`-valued functions.
4. **Experiments** (`Foundations/Experiments.lean`): `invProb`, `predProb`,
   `acceptProb`, `distAdv`. Bit strings are `Fin n → Bool`.
5. **Non-uniformity in the concrete layer** (the hybrid index `k`, `i*, j*`, guessed
   values) appears as an explicit parameter of `B` together with an existence or
   averaging statement; the asymptotic layer moves it into advice.
6. **Structural efficiency.** Each concrete reduction's docstring records what `B` does
   with `A` (number of calls, extra sampling, extra computation), which is exactly what
   the asymptotic layer must charge.
7. **Oracle adversaries** (PRFs) are explicit adaptive query trees with a bound on the
   number of queries, defined in the PRF development.

## Errors and gaps in the source to handle

* §1.3 states "the discrete-log assumption implies the CDH and the DDH assumptions";
  as assumptions the implications go the other way (DDH ⇒ CDH ⇒ DL), which is what
  Figure 1.1 says.
* Theorem 2.1: the reduction repeats `T = 4n² / (α μ)` times, polynomial only where `μ`
  is large. The formal reduction fixes `T` from one inverse-polynomial lower bound that
  holds infinitely often.
* Theorem 3.3 (GGM): the `(j*+1)`-th query *can* repeat an earlier prefix; the two
  sub-hybrids then agree on that event. The formal proof splits the cases.
* The margin box "Lemma 2.2" in §2.3 is a garbled copy of Lemma 2.1's proof.

Found during formalization (each recorded in the relevant docstring):

* §2.2.1: the example `g(x₁‖x₂) = x₁‖x₂` when `x₁ = 0^{n/2}` is *not* one-way for every
  one-way `f` (counterexample: the `f` of §2.2.2, `invProb_zeroPatch_eq_one`). The general
  robustness bound needs an extra term or a correction map (`invProb_patch_le`,
  `invProb_patch_le_of_correction`).
* §2.2.2: `f∘f` is the constant `0ⁿ‖g(0ⁿ)`, not `0^{2n}`; `B` must output `x₁`. Claim 2.1
  writes `g(y)` for `h(y)` and `g⁻¹` for `g'⁻¹`; Claim 2.2's middle step is unjustified
  (its final bound holds). Lemma 2.3 writes `μ_{B,g}` for `μ_{B,f}`.
* Theorem 2.1: the step `q·θ = μ/2` fails for `q = ⌈2n/α⌉`; repaired with `θ = μ₀/(2q)`.
* Claim 2.3 applies the `n`-bit `f` to `n − 1` bits. Figure 2.5 includes `L = ∅`, whose
  XOR is the constant `0`; only nonempty `L` are used, giving `ε³/(16n)` instead of
  `ε³/(8n)`.
* Lemma 3.3: the reduction `A(X…, Z, Y…)` contradicts the hybrids, which put the `Y`s
  first.
* Theorem 3.3 (GGM): besides the repeated-prefix gap, the outer adversary answers only the
  `(j*+1)`-th query with the challenge, so later queries with the same prefix are
  inconsistent with it; the formal `B` answers every query with that prefix from the
  challenge, after which no case split is needed.

## Phase A: concrete layer (complete)

| Workstream | Files | Content |
| --- | --- | --- |
| foundations | `Cryptography/Foundations/{Negligible,Probability,Experiments}.lean` | fill all proofs: negligible closure, `2^{-n}`, the neither example; uniform probability laws, union bound, Fubini, averaging (Lemma 2.1), hybrid lemma; advantage ≤ SD (Lemma 3.1) |
| one-way | `Cryptography/OneWayFunctions/` | §2.2 robustness and brittleness (`f∘f`, dropped bit, Claims 2.1–2.2, Lemma 2.3 padding); Theorem 2.1 Yao amplification |
| goldreich-levin | `Cryptography/HardcoreBit/` | pairwise independence and Chebyshev (Theorem 2.4); Claim 2.3; Theorem 2.3 in the three cases |
| prg | `Cryptography/Pseudorandom/{Indistinguishability,Generators}.lean` | sunglass and multicopy (Lemmas 3.2, 3.3); PRG extension (Theorem 3.1); PRG from a one-way permutation (Theorem 3.2) |
| ggm | `Cryptography/Pseudorandom/Functions/` | oracle query trees, random functions, Definitions 3.6–3.9, GGM (Theorem 3.3) |

### Completion record

Completed 2026-10-14 by five parallel workstreams (`garg/{foundations,oneway,gl,prg,ggm}`),
merged into `cryptography/garg-ch1-3`. Verified with shell `lake build` (user-approved
deviation from `AGENTS.md`, as for the earlier cryptography work): the full `TCSlib`
builds with no errors; no `sorry` in `Cryptography/{Foundations,OneWayFunctions,
HardcoreBit,Pseudorandom}`; `style_lint.py --area` reports 0 findings in all 23 files and
the four facades. `audits/garg-ch1-3/Checks.lean`: all 41 headline theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`. One merge fix: the PRG and GGM workstreams
both defined `acceptProb_comp_equiv`; it now lives once in `Foundations/Experiments.lean`.

Headlines: `yao_amplification(_exp)` (Thm 2.1); `invProb_perfectInverter`,
`invProb_majorityInverter`, `invProb_guessInverter(_cubic)` (Thm 2.3, cases i–iii);
`chebyshev_pairwise_ident` (Thm 2.4); `distAdv_le_statDist` (Lemma 3.1);
`distAdv_sunglassRed`, `exists_multicopyRed_ge` (Lemmas 3.2–3.3); `exists_prgExtRed_ge`
(Thm 3.1); `exists_owpPredictor` (Thm 3.2); `QueryTree.uprob_evalLazy` (lazy sampling);
`ggm_prfAdv_le`, `exists_ggm_dist` (Thm 3.3). Each reduction's docstring records what the
asymptotic layer must charge. The external audit gate has not been conducted.

## Phase B: asymptotic layer (blocked on complexity work)

Needs: probabilistic machines with coins; non-uniform PPT as machine + polynomial
advice + coins + time; closure of non-uniform PPT under pre/post-processing,
advice hard-wiring, sampling (`{0,1}ⁿ` and `[q]`), polynomially many calls with fresh
coins, XOR/equality/inner product/majority; clocked universal simulation (Levin);
oracle adversaries with string answers and lazy sampling; fixed output length and
two-argument polynomial-time functions; efficiently samplable ensembles. Then:
Definitions 1.1, 1.2, 2.1–2.3, 3.4, 3.5, 3.8, 3.9 and the asymptotic theorems; Levin's
one-way function (Theorem 2.2).

## Deferred

§1.3 number theory (DL/CDH/DDH examples, the Legendre-symbol DDH attack in `Z_p^*`,
Lemma 1.1 CDH in `QR_N` implies factoring) and Naor–Reingold (§3.5).
