/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The randomized complexity classes BPP, RP, coRP, ZPP

Verifier-style definitions of Arora–Barak's randomized complexity classes,
following the certificate view of [AB09, Def 7.4]: a language is in a
randomized class when some efficient two-input predicate `M(x, r)`, run on the
input `x` and a uniformly random string `r` of polynomially-bounded length,
decides membership with the class's acceptance-probability profile.

## Main definitions

* `Randomized.randProb` — the probability of an event over a uniform random
  string of a given length, as a rational counting ratio.
* `Randomized.VerifierModel` — an abstract *efficiency notion* standing in for
  "polynomial-time Turing machine" (see **Deviations** below).
* `Randomized.InBPP` — [AB09, Def 7.4] (equivalently Def 7.1 via the
  certificate view).
* `Randomized.InRP`, `Randomized.InCoRP` — [AB09, Def 7.6] and the remark
  following it.
* `Randomized.InZPP` — [AB09, Def 7.7], in the zero-error "abort"
  formulation (see **Deviations**).
* `Randomized.raceVerifier`, `Randomized.majorityVerifier` — the two verifier
  constructions used by Theorems 7.8 and 7.10.

## Main results (sorry-stubbed)

* `Randomized.inZPP_iff_inRP_and_inCoRP` — `ZPP = RP ∩ coRP` [AB09, Thm 7.8].
* `Randomized.bpp_error_reduction` — error reduction [AB09, Thm 7.10].
* `Randomized.inBPPWeak_iff_inBPP` — `BPP_{n^{-c}} = BPP` [AB09, Lem 7.9].

## Deviations from the source

* **Machine model.** [AB09] defines these classes with polynomial-time Turing
  machines.  Per the repository's agreed scope, we use the certificate view of
  [AB09, Def 7.4] — predicates over inputs and random strings — and replace
  "`M` is a polynomial-time TM" by membership in an abstract
  `VerifierModel` `E`, a predicate on verifiers.  Every class and theorem is
  parametrized by `E`.  The closure properties that [AB09]'s proofs use
  (building the race, majority, and projection verifiers out of given ones)
  are stated as explicit named hypotheses (`ClosedUnder…`), all of which hold
  for the intended instantiation "computable in polynomial time"; a future
  computability layer can instantiate `E` and discharge them.
* **Probability.** `Pr_{r ∈ {0,1}^m}` is the counting ratio
  `#{r : accepted}/2^m` valued in `ℚ`; random strings of length `m` are
  `Fin m → Bool`, passed to verifiers as lists via `List.ofFn`.
* **ZPP.** [AB09, Def 7.7] defines `ZPP` by expected running time of a
  zero-error machine.  Expected time is not expressible for abstract
  predicates, so we use the standard equivalent "Las Vegas" formulation: a
  verifier with values in `Option Bool` that is never wrong and outputs `none`
  ("don't know") with probability at most `1/2`.  [AB09, §7.4.2] sketches the
  equivalence of expected-time and worst-case formulations (truncation via
  Markov's inequality).
* The constant `2/3` follows [AB09, Defs 7.1/7.6]; `1/2` in `InZPP` is the
  conventional choice (any constant in `(0,1)` gives the same class, by the
  same repetition argument as [AB09, §7.4.1]).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

/-- The probability, over a uniformly random string `r ∈ {0,1}^m`, that the
event `A` holds of `r` (as a list): the counting ratio `#{r : A r}/2^m`.
[AB09, Def 7.4: "`Pr_{r ∈_R {0,1}^{p(|x|)}}`"] -/
def randProb (m : ℕ) (A : List Bool → Prop) [DecidablePred A] : ℚ :=
  ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) / 2 ^ m

/-- A function `p : ℕ → ℕ` is polynomially bounded.  Written in the
`a * (n+1)^k` normal form used by `CircuitComplexity.PPoly`. -/
def PolyGrowth (p : ℕ → ℕ) : Prop :=
  ∃ a k : ℕ, ∀ n, p n ≤ a * (n + 1) ^ k

/-- An abstract *efficiency notion* for verifiers, standing in for
"polynomial-time Turing machine" in [AB09, Def 7.4] (see the module
docstring's **Deviations**).  `Eff M` reads "`M` is an efficient verifier";
verifiers are `Option Bool`-valued so that zero-error ("don't know") verifiers
and ordinary Boolean verifiers share one notion.  `EffTwoWitness N` is the
corresponding notion for predicates of an input and two witness strings, the
verifier format of `Σ₂`-statements (used by [AB09, Thm 7.18]). -/
structure VerifierModel where
  /-- "`M` is an efficient (poly-time) verifier." -/
  Eff : (List Bool → List Bool → Option Bool) → Prop
  /-- "`N` is an efficient (poly-time) two-witness predicate." -/
  EffTwoWitness : (List Bool → List Bool → List Bool → Bool) → Prop

/-- A Boolean verifier, viewed as an `Option Bool`-valued one. -/
def boolVerifier (M : List Bool → List Bool → Bool) :
    List Bool → List Bool → Option Bool :=
  fun x r => some (M x r)

variable (E : VerifierModel)

/-- `L ∈ BPP`: some efficient verifier `M` with polynomially-bounded
randomness decides `L` with two-sided error at most `1/3` — for every input
`x`, `Pr_{r ∈ {0,1}^{p(|x|)}}[M(x,r) = L(x)] ≥ 2/3`.  [AB09, Def 7.4]
(the certificate form of [AB09, Def 7.1]). -/
def InBPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (p : ℕ → ℕ),
    E.Eff (boolVerifier M) ∧ PolyGrowth p ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (p x.length) fun r => M x r = true) ∧
      (x ∉ L → 2/3 ≤ randProb (p x.length) fun r => M x r = false)

/-- `L ∈ RP`: one-sided error — inputs in `L` are accepted with probability
at least `2/3`, inputs outside `L` are *never* accepted.  [AB09, Def 7.6] -/
def InRP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (p : ℕ → ℕ),
    E.Eff (boolVerifier M) ∧ PolyGrowth p ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (p x.length) fun r => M x r = true) ∧
      (x ∉ L → ∀ r : Fin (p x.length) → Bool, M x (List.ofFn r) = false)

/-- `L ∈ coRP` iff its complement is in `RP`: one-sided error in the other
direction.  [AB09, §7.3: "`coRP = {L | L̄ ∈ RP}`"] -/
def InCoRP (L : Language Bool) : Prop :=
  InRP E Lᶜ

/-- `L ∈ ZPP`: some efficient zero-error verifier decides `L` — it may output
`none` ("don't know") with probability at most `1/2`, but whenever it outputs
an answer, the answer is correct.  [AB09, Def 7.7], in the equivalent
Las Vegas formulation (see the module docstring's **Deviations**). -/
def InZPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ),
    E.Eff M ∧ PolyGrowth p ∧
    ∀ x : List Bool,
      (x ∈ L → ∀ r : Fin (p x.length) → Bool, M x (List.ofFn r) ≠ some false) ∧
      (x ∉ L → ∀ r : Fin (p x.length) → Bool, M x (List.ofFn r) ≠ some true) ∧
      randProb (p x.length) (fun r => M x r = none) ≤ 1/2

section Constructions

/-- The *race* of an `RP` verifier for `L` and an `RP` verifier for `Lᶜ` on
split randomness: on `r = r₁ ++ r₂`, answer `some true` if `M₁` accepts `r₁`,
else `some false` if `M₂` accepts `r₂`, else `none`.  The construction behind
`RP ∩ coRP ⊆ ZPP` in [AB09, Thm 7.8]. -/
def raceVerifier (M₁ M₂ : List Bool → List Bool → Bool) (p₁ : ℕ → ℕ) :
    List Bool → List Bool → Option Bool := fun x r =>
  if M₁ x (r.take (p₁ x.length)) then some true
  else if M₂ x (r.drop (p₁ x.length)) then some false
  else none

/-- The `k`-fold repetition of a verifier with majority vote, on randomness
split into `k` blocks of length `p(|x|)`: the construction behind error
reduction [AB09, Thm 7.10]. -/
def majorityVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  let n := x.length
  let votes := (List.range (k n)).countP fun i =>
    M x ((r.drop (i * p n)).take (p n))
  k n < 2 * votes

/-- `E` can race two of its Boolean verifiers (closure of polynomial time
under running two machines on split randomness). -/
def ClosedUnderRace : Prop :=
  ∀ M₁ M₂ p₁, E.Eff (boolVerifier M₁) → E.Eff (boolVerifier M₂) →
    E.Eff (raceVerifier M₁ M₂ p₁)

/-- `E` can turn a zero-error verifier into the Boolean verifier answering
"did it output `some b`?" (closure of polynomial time under postprocessing
the output). -/
def ClosedUnderAnswerIs : Prop :=
  ∀ M b, E.Eff M →
    E.Eff (boolVerifier fun x r => M x r = some b)

/-- `E` can repeat a Boolean verifier polynomially many times and take the
majority (closure of polynomial time under polynomial repetition). -/
def ClosedUnderMajority : Prop :=
  ∀ M p k, E.Eff (boolVerifier M) → PolyGrowth k →
    E.Eff (boolVerifier (majorityVerifier M p k))

end Constructions

/-- **`ZPP = RP ∩ coRP`** ([AB09, Thm 7.8]).  Stated relative to the
efficiency notion `E`, under the closure properties the two directions use.

**Proof sketch.** (⊆) A zero-error verifier yields an `RP` verifier by
answering `true` exactly on output `some true`: inputs outside `L` are never
accepted (zero error), and inputs in `L` are accepted whenever the verifier
does not abort, which has probability at least `1/2`; amplify `1/2` to `2/3`
by one repetition (absorbed into the majority closure).  Symmetrically with
`some false` for `Lᶜ`, giving `coRP`.  (⊇) Race an `RP` verifier `M₁` for `L`
against an `RP` verifier `M₂` for `Lᶜ` on split randomness
(`raceVerifier`): a definite answer is never wrong, since `M₁` accepting
certifies `x ∈ L` and `M₂` accepting certifies `x ∉ L`; and whichever of the
two is the "live" verifier for `x` accepts with probability ≥ `2/3`, so the
race aborts with probability at most `1/3 ≤ 1/2`. -/
theorem inZPP_iff_inRP_and_inCoRP (hRace : ClosedUnderRace E)
    (hAns : ClosedUnderAnswerIs E) (hMaj : ClosedUnderMajority E)
    (L : Language Bool) :
    InZPP E L ↔ InRP E L ∧ InCoRP E L := by
  sorry

/-- `L ∈ BPP_{n^{-c}}`: like `InBPP`, but with success probability only
`1/2 + |x|^{-c}` — formally, `1/2 + (|x|+1)^{-c}` to avoid the degenerate
division at `|x| = 0` (deviation: the book writes `|x|^{-c}`, which is
ill-defined on the empty input).  [AB09, Lem 7.9] -/
def InBPPWeak (c : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (p : ℕ → ℕ),
    E.Eff (boolVerifier M) ∧ PolyGrowth p ∧
    ∀ x : List Bool,
      (x ∈ L → 1/2 + ((x.length + 1 : ℚ))⁻¹ ^ c ≤
        randProb (p x.length) fun r => M x r = true) ∧
      (x ∉ L → 1/2 + ((x.length + 1 : ℚ))⁻¹ ^ c ≤
        randProb (p x.length) fun r => M x r = false)

/-- `L ∈ BPP` with error at most `2^{-(|x|+1)^d}` — the amplified form
produced by error reduction.  (The exponent `(|x|+1)^d ≥ |x|^d` strengthens
[AB09, Thm 7.10]'s `2^{-|x|^d}` uniformly in `|x|`.) -/
def InBPPStrong (d : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (p : ℕ → ℕ),
    E.Eff (boolVerifier M) ∧ PolyGrowth p ∧
    ∀ x : List Bool,
      (x ∈ L → 1 - (1/2 : ℚ) ^ (x.length + 1) ^ d ≤
        randProb (p x.length) fun r => M x r = true) ∧
      (x ∉ L → 1 - (1/2 : ℚ) ^ (x.length + 1) ^ d ≤
        randProb (p x.length) fun r => M x r = false)

/-- **Error reduction** ([AB09, Thm 7.10]).  A language decidable with
success probability `1/2 + |x|^{-c}` is decidable with success probability
`1 − 2^{-|x|^d}`, for every constant `d` — relative to `E`, assuming `E` is
closed under polynomial majority repetition.

**Proof sketch.** Run the weak verifier `k = 8·(n+1)^{2d+c}` times on
independent blocks of randomness and take the majority
(`majorityVerifier`).  The votes are i.i.d. Bernoulli with success
probability `p ≥ 1/2 + (n+1)^{-c}`, so by the Chernoff bound
([AB09, Cor 7.11]; `Randomized.majority_error_le` in
`Randomized.ErrorReduction`, transported from the product measure to the
counting probability `randProb`) the majority errs with probability at most
`e^{−(n+1)^{-2c}·p·k/16} ≤ 2^{-(n+1)^d}`. -/
theorem bpp_error_reduction (hMaj : ClosedUnderMajority E) {c : ℕ}
    {L : Language Bool} (hL : InBPPWeak E c L) (d : ℕ) :
    InBPPStrong E d L := by
  sorry

/-- **`BPP_{n^{-c}} = BPP`** ([AB09, Lem 7.9]): the success threshold `2/3`
in the definition of `BPP` can be weakened to `1/2 + |x|^{-c}` without
changing the class.

**Proof sketch.** `BPP ⊆ BPP_{n^{-c}}` since `2/3 ≥ 1/2 + (n+1)^{-c}` for
all but finitely many `n` — and for the finitely many small `n` the weak
threshold still follows from `2/3` once `c ≥ 2` (for `c < 2` adjust by one
round of majority amplification, absorbed in `hMaj`).  The converse applies
`bpp_error_reduction` with `d = 1` and weakens `1 − 2^{-(n+1)}` to `2/3`. -/
theorem inBPPWeak_iff_inBPP (hMaj : ClosedUnderMajority E) (c : ℕ)
    (L : Language Bool) :
    InBPPWeak E c L ↔ InBPP E L := by
  sorry

end Randomized
