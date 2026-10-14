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

## Phase A: concrete layer (in progress)

| Workstream | Files | Content |
| --- | --- | --- |
| foundations | `Cryptography/Foundations/{Negligible,Probability,Experiments}.lean` | fill all proofs: negligible closure, `2^{-n}`, the neither example; uniform probability laws, union bound, Fubini, averaging (Lemma 2.1), hybrid lemma; advantage ≤ SD (Lemma 3.1) |
| one-way | `Cryptography/OneWayFunctions/` | §2.2 robustness and brittleness (`f∘f`, dropped bit, Claims 2.1–2.2, Lemma 2.3 padding); Theorem 2.1 Yao amplification |
| goldreich-levin | `Cryptography/HardcoreBit/` | pairwise independence and Chebyshev (Theorem 2.4); Claim 2.3; Theorem 2.3 in the three cases |
| prg | `Cryptography/Pseudorandom/{Indistinguishability,Generators}.lean` | sunglass and multicopy (Lemmas 3.2, 3.3); PRG extension (Theorem 3.1); PRG from a one-way permutation (Theorem 3.2) |
| ggm | `Cryptography/Pseudorandom/Functions/` | oracle query trees, random functions, Definitions 3.6–3.9, GGM (Theorem 3.3) |

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
