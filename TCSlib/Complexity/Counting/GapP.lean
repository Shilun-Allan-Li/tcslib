/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Complexity.Counting.PP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gap functions

A *gap function* counts accepting minus rejecting computations: for a nondeterministic machine
`M`, `f(x) = #accept(x) - #reject(x)`, and GapP is the class of such `f` for polynomial-time `M`
[Wat08, §IV.5], [FR99, §2]. GapP is closed under sums, products and negation, which is what makes
it the right tool for bounding quantum classes (plan item Q4.5). Gap functions are integer-valued,
so the bridge goes through scaled numerators, not raw gate entries: the entries `1/√2` of `H` and
`i` of `S` are not integers. For a circuit over the gate set of [Wat08, §III.2] with `h` Hadamard
gates, every amplitude is `(1/√2)^h` times a sum of terms in `{±1, ±i}` (plan FD-10). The real and
imaginary parts of these sums are integers, and the acceptance probability, a sum of squared
moduli, is `F(x) / 2^h` for an integer `F` built from them. It is such numerators `F`, with the
denominator stated explicitly, that the later construction shows to be gap functions
[Wat08, §IV.5].

Here a computation is a random string `r` of the length the schedule `polyLen a k` assigns, and
the verifier answers `some true` (accept), `some false` (reject) or `none` (abstain). Abstaining
strings count for neither side. Abstention is what makes exact closure under sums possible with
fixed-length random strings: for a verifier that never abstains, the gap at any length `m ≥ 1` is
even (it is `2 · #accept - 2^m`), and padding a verifier to a longer schedule multiplies its gap
by a power of `2`. With abstention, padding is free (`gap_padVerifier`).

## Main definitions

* `Counting.gap M m x` — `#{r ∈ {0,1}^m : M x r = some true} - #{r : M x r = some false}`.
* `Counting.IsGapP E f` — `f` is the gap of an efficient verifier on a polynomial schedule.
* The combinators `negVerifier`, `padVerifier`, `sumVerifier`, `prodVerifier`,
  `constVerifier`, `coinFill`, and the closure hypotheses `ClosedUnderGapNeg`,
  `ClosedUnderPad`, `ClosedUnderGapSum`, `ClosedUnderGapProd`, `HasConstVerifiers`,
  `ClosedUnderCoinFill`, in the style of `Randomized.ClosedUnderMajority`.

## Main results

* `Counting.gap_negVerifier`, `gap_padVerifier`, `gap_sumVerifier`, `gap_prodVerifier`,
  `gap_constVerifier` — how each combinator acts on gaps.
* `Counting.IsGapP.neg`, `IsGapP.add`, `IsGapP.mul`, `isGapP_one`, `isGapP_neg_one` — GapP is
  closed under negation, sums and products, and contains `±1` [FR99, §2].
* `Counting.inPP_iff_exists_isGapP` — `L ∈ PP` iff membership is the sign of a gap function
  [Wat08, §IV.5].

## Divergences

* [Wat08, §IV.5] and [FR99] define GapP through polynomial-time nondeterministic machines. Here
  the machine is an abstract verifier in a `VerifierModel`, as for `Randomized.InBPP`, and the
  computation paths are the random strings of one length. The closure properties the proofs
  need are explicit hypotheses on the model; `Counting/PolyTime.lean` states that
  `Randomized.polyTimeModel` satisfies them.

## References

* [Wat08] J. Watrous, *Quantum Computational Complexity*, arXiv:0804.3401, 2008.
* [FR99] L. Fortnow, J. Rogers, *Complexity limitations on quantum computation*, Journal of
  Computer and System Sciences 59(2), 240–252, 1999.
-/

namespace Counting

open Randomized Finset

/-! ### Gaps -/

/-- The *gap* of the verifier `M` on input `x` over random strings of length `m`: the number of
strings it accepts minus the number it rejects; abstentions (`none`) count for neither.
[Wat08, §IV.5], [FR99, §2] -/
def gap (M : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) : ℤ :=
  ((univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = some true).card : ℤ) -
    ((univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = some false).card : ℤ)

/-- `gap M m x` is the number of accepted strings minus the number of rejected strings. -/
theorem gap_eq (M : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) :
    gap M m x =
      ((univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = some true).card : ℤ) -
        ((univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = some false).card : ℤ) := rfl

/-- `f` is a *gap function* (in GapP) relative to the verifier model `E`: it is the gap of an
efficient verifier on the schedule `polyLen a k`. [Wat08, §IV.5], [FR99, §2], in the form of the
module docstring. -/
def IsGapP (E : VerifierModel) (f : List Bool → ℤ) : Prop :=
  ∃ (M : List Bool → List Bool → Option Bool) (a k : ℕ),
    E.Eff M ∧ ∀ x : List Bool, f x = gap M (polyLen a k x.length) x

/-- `f ∈ GapP` iff `f` is the gap of an efficient verifier on a polynomial schedule. -/
theorem isGapP_iff (E : VerifierModel) (f : List Bool → ℤ) :
    IsGapP E f ↔
      ∃ (M : List Bool → List Bool → Option Bool) (a k : ℕ),
        E.Eff M ∧ ∀ x : List Bool, f x = gap M (polyLen a k x.length) x := Iff.rfl

/-- The gap of a Boolean verifier (one that never abstains) is determined by its acceptance
probability: `gap = 2^m · (2 · Pr[accept] - 1)`.

**Proof sketch.** With no abstentions, `#reject = 2^m - #accept`
(`card_univ_bitstrings`, `Finset.filter_card_add_filter_neg_card_eq_card`), so the gap is
`2 · #accept - 2^m`; and `randProb m _ = #accept / 2^m` by definition. -/
theorem gap_boolVerifier (M : List Bool → List Bool → Bool) (m : ℕ) (x : List Bool) :
    (gap (boolVerifier M) m x : ℚ) = 2 ^ m * (2 * randProb m (fun r => M x r = true) - 1) := by
  sorry

/-- The gap of a Boolean verifier, in integers: twice the number of accepted strings minus `2^m`
(round-1 audit, sanity statement 5).

**Proof sketch.** With no abstentions, `#reject = 2^m - #accept`, as in `gap_boolVerifier`. -/
theorem gap_boolVerifier_int (M : List Bool → List Bool → Bool) (m : ℕ) (x : List Bool) :
    gap (boolVerifier M) m x =
      2 * ((univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = true).card : ℤ) - 2 ^ m := by
  sorry

/-- A gap on length `m` is at most `2^m` in absolute value (round-1 audit, sanity statement 5).

**Proof sketch.** The accepted and rejected strings are disjoint sets of the `2^m` strings, so
each count is between `0` and `2^m`, and their difference is too. -/
theorem abs_gap_le (M : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) :
    |gap M m x| ≤ 2 ^ m := by
  sorry

/-! ### Verifier combinators -/

/-- Swap acceptance and rejection, keeping abstentions. -/
def negVerifier (M : List Bool → List Bool → Option Bool) :
    List Bool → List Bool → Option Bool := fun x r => (M x r).map (!·)

/-- `negVerifier M` answers `(M x r).map not`. -/
theorem negVerifier_eq (M : List Bool → List Bool → Option Bool) (x r : List Bool) :
    negVerifier M x r = (M x r).map (!·) := rfl

/-- Pad `M` to longer random strings: run `M` on the first `p |x|` bits if every later bit is
`false`, and abstain otherwise. On any length `m ≥ p |x|` the gap is unchanged
(`gap_padVerifier`). -/
def padVerifier (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) :
    List Bool → List Bool → Option Bool := fun x r =>
  if (r.drop (p x.length)).all (fun b => !b) then M x (r.take (p x.length)) else none

/-- `padVerifier M p` runs `M` on the first `p |x|` bits when the rest are all `false`, and
abstains otherwise. -/
theorem padVerifier_eq (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) (x r : List Bool) :
    padVerifier M p x r =
      if (r.drop (p x.length)).all (fun b => !b) then M x (r.take (p x.length)) else none := rfl

/-- The *sum* of two verifiers: the first random bit chooses which verifier runs on the rest. On
length `m + 1` its gap is the sum of the two gaps on length `m` (`gap_sumVerifier`). -/
def sumVerifier (M₁ M₂ : List Bool → List Bool → Option Bool) :
    List Bool → List Bool → Option Bool := fun x r =>
  match r with
  | [] => none
  | b :: r' => if b then M₁ x r' else M₂ x r'

/-- `sumVerifier M₁ M₂` abstains on the empty string and otherwise runs `M₁` or `M₂` on the tail,
as the first bit is `true` or `false`. -/
theorem sumVerifier_eq (M₁ M₂ : List Bool → List Bool → Option Bool) (x r : List Bool) :
    sumVerifier M₁ M₂ x r =
      match r with
      | [] => none
      | b :: r' => if b then M₁ x r' else M₂ x r' := rfl

/-- The *product* of two verifiers: run `M₁` on the first `p |x|` bits and `M₂` on the rest;
accept if both give the same answer, reject if they give different answers, abstain if either
abstains. Its gap is the product of the two gaps (`gap_prodVerifier`). -/
def prodVerifier (M₁ M₂ : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) :
    List Bool → List Bool → Option Bool := fun x r =>
  match M₁ x (r.take (p x.length)), M₂ x (r.drop (p x.length)) with
  | some b₁, some b₂ => some (b₁ == b₂)
  | _, _ => none

/-- `prodVerifier M₁ M₂ p` combines `M₁` on the first `p |x|` bits and `M₂` on the rest: same
answers accept, different answers reject, any abstention abstains. -/
theorem prodVerifier_eq (M₁ M₂ : List Bool → List Bool → Option Bool) (p : ℕ → ℕ)
    (x r : List Bool) :
    prodVerifier M₁ M₂ p x r =
      match M₁ x (r.take (p x.length)), M₂ x (r.drop (p x.length)) with
      | some b₁, some b₂ => some (b₁ == b₂)
      | _, _ => none := rfl

/-- The *constant* verifier with answer `b`: answer `some b` on the all-`false` string and
abstain on every other. Its gap is `1` if `b` and `-1` otherwise, at every length. -/
def constVerifier (b : Bool) : List Bool → List Bool → Option Bool := fun _ r =>
  if r.all (fun c => !c) then some b else none

/-- `constVerifier b` answers `some b` exactly on all-`false` strings. -/
theorem constVerifier_eq (b : Bool) (x r : List Bool) :
    constVerifier b x r = if r.all (fun c => !c) then some b else none := rfl

/-- Turn a verifier that may abstain into a Boolean one: run `M` on the first `p |x|` bits, and
where it abstains, answer the next random bit instead, or `false` if the string has no next bit.
Later bits are ignored. On random strings of any length `m ≥ p |x| + 1`, so that the next bit
exists, its acceptance probability is `1/2 + gap / 2^(p |x| + 1)` (`randProb_coinFill`). On
shorter strings the `false` default applies and that formula fails (round-1 audit, finding 5). -/
def coinFill (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  (M x (r.take (p x.length))).getD ((r.drop (p x.length)).headD false)

/-- `coinFill M p` answers `M`'s answer on the first `p |x|` bits, or the next bit if `M`
abstains. -/
theorem coinFill_eq (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) (x r : List Bool) :
    coinFill M p x r = (M x (r.take (p x.length))).getD ((r.drop (p x.length)).headD false) :=
  rfl

/-! ### How the combinators act on gaps -/

/-- Negating a verifier negates its gap.

**Proof sketch.** `negVerifier M x r = some true` iff `M x r = some false`, and vice versa, so
the two counts swap. -/
theorem gap_negVerifier (M : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) :
    gap (negVerifier M) m x = - gap M m x := by
  sorry

/-- Padding does not change the gap: on any length `m ≥ p |x|`, `padVerifier M p` has the gap of
`M` on length `p |x|`.

**Proof sketch.** Split each string of length `m` as `r₁ ++ r₂` with `|r₁| = p |x|`
(`Fin.append`-style bijection `(Fin m → Bool) ≃ (Fin (p |x|) → Bool) × (Fin (m - p |x|) → Bool)`).
Only `r₂ = 0…0` gives a non-abstaining answer, namely `M x r₁`, so both counts equal those of `M`
on length `p |x|`. -/
theorem gap_padVerifier (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) {m : ℕ}
    (x : List Bool) (h : p x.length ≤ m) :
    gap (padVerifier M p) m x = gap M (p x.length) x := by
  sorry

/-- The sum verifier adds gaps: on length `m + 1`, its gap is the gap of `M₁` plus the gap of
`M₂`, both on length `m`.

**Proof sketch.** Split strings of length `m + 1` by their first bit (`Fin.consEquiv`). Strings
starting with `true` contribute `M₁`'s counts on the tail and strings starting with `false`
contribute `M₂`'s. -/
theorem gap_sumVerifier (M₁ M₂ : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) :
    gap (sumVerifier M₁ M₂) (m + 1) x = gap M₁ m x + gap M₂ m x := by
  sorry

/-- The product verifier multiplies gaps: on length `p |x| + m`, its gap is the gap of `M₁` on
length `p |x|` times the gap of `M₂` on length `m`.

**Proof sketch.** Split strings as `r₁ ++ r₂` as in `gap_padVerifier`. The answer is accept when
the two answers agree and reject when they differ, so with `s(true) = 1`, `s(false) = -1`,
`s(none) = 0`, the gap is `∑_{r₁, r₂} s(M₁ r₁) · s(M₂ r₂) = (∑ s(M₁ r₁)) · (∑ s(M₂ r₂))`. -/
theorem gap_prodVerifier (M₁ M₂ : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) (m : ℕ)
    (x : List Bool) :
    gap (prodVerifier M₁ M₂ p) (p x.length + m) x = gap M₁ (p x.length) x * gap M₂ m x := by
  sorry

/-- The constant verifier with answer `b` has gap `1` if `b = true` and `-1` if `b = false`, on
every length.

**Proof sketch.** Exactly one string of each length is all-`false`, and it is the only string on
which the verifier answers. -/
theorem gap_constVerifier (b : Bool) (m : ℕ) (x : List Bool) :
    gap (constVerifier b) m x = if b then 1 else -1 := by
  sorry

/-- The acceptance probability of `coinFill M p` on any length `m ≥ p |x| + 1` is
`1/2 + gap / 2^(p |x| + 1)`, where `gap` is the gap of `M` on length `p |x|`. In particular it is
above `1/2` exactly when the gap is positive.

**Proof sketch.** Bits after position `p |x|` are ignored, so reduce to `m = p |x| + 1`. With
`T`, `F`, `N` the numbers of accepting, rejecting and abstaining strings of length `p |x|`, the
accepting strings of length `p |x| + 1` number `2T + N`, and `T + F + N = 2^(p |x|)`; so the
probability is `(2T + N) / 2^(p |x| + 1) = 1/2 + (T - F) / 2^(p |x| + 1)`. -/
theorem randProb_coinFill (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) {m : ℕ}
    (x : List Bool) (h : p x.length + 1 ≤ m) :
    randProb m (fun r => coinFill M p x r = true) =
      1/2 + (gap M (p x.length) x : ℚ) / 2 ^ (p x.length + 1) := by
  sorry

/-! ### Closure hypotheses on a verifier model -/

/-- `E` can negate a verifier (swap acceptance and rejection). -/
def ClosedUnderGapNeg (E : VerifierModel) : Prop :=
  ∀ M, E.Eff M → E.Eff (negVerifier M)

/-- `ClosedUnderGapNeg E` unfolds to closure of `E.Eff` under `negVerifier`. -/
theorem closedUnderGapNeg_iff (E : VerifierModel) :
    ClosedUnderGapNeg E ↔ ∀ M, E.Eff M → E.Eff (negVerifier M) := Iff.rfl

/-- `E` can pad a verifier to the schedule `n ↦ polyLen a k n + c`. -/
def ClosedUnderPad (E : VerifierModel) : Prop :=
  ∀ M (a k c : ℕ), E.Eff M → E.Eff (padVerifier M fun n => polyLen a k n + c)

/-- `ClosedUnderPad E` unfolds to closure of `E.Eff` under `padVerifier` on shifted polynomial
schedules. -/
theorem closedUnderPad_iff (E : VerifierModel) :
    ClosedUnderPad E ↔
      ∀ M (a k c : ℕ), E.Eff M → E.Eff (padVerifier M fun n => polyLen a k n + c) := Iff.rfl

/-- `E` can form the sum of two of its verifiers. -/
def ClosedUnderGapSum (E : VerifierModel) : Prop :=
  ∀ M₁ M₂, E.Eff M₁ → E.Eff M₂ → E.Eff (sumVerifier M₁ M₂)

/-- `ClosedUnderGapSum E` unfolds to closure of `E.Eff` under `sumVerifier`. -/
theorem closedUnderGapSum_iff (E : VerifierModel) :
    ClosedUnderGapSum E ↔ ∀ M₁ M₂, E.Eff M₁ → E.Eff M₂ → E.Eff (sumVerifier M₁ M₂) := Iff.rfl

/-- `E` can form the product of two of its verifiers, split at a polynomial point. -/
def ClosedUnderGapProd (E : VerifierModel) : Prop :=
  ∀ M₁ M₂ (a k : ℕ), E.Eff M₁ → E.Eff M₂ → E.Eff (prodVerifier M₁ M₂ (polyLen a k))

/-- `ClosedUnderGapProd E` unfolds to closure of `E.Eff` under `prodVerifier` at polynomial
split points. -/
theorem closedUnderGapProd_iff (E : VerifierModel) :
    ClosedUnderGapProd E ↔
      ∀ M₁ M₂ (a k : ℕ), E.Eff M₁ → E.Eff M₂ → E.Eff (prodVerifier M₁ M₂ (polyLen a k)) :=
  Iff.rfl

/-- `E` contains both constant verifiers. -/
def HasConstVerifiers (E : VerifierModel) : Prop := ∀ b, E.Eff (constVerifier b)

/-- `HasConstVerifiers E` says `E.Eff (constVerifier b)` for both `b`. -/
theorem hasConstVerifiers_iff (E : VerifierModel) :
    HasConstVerifiers E ↔ ∀ b, E.Eff (constVerifier b) := Iff.rfl

/-- `E` can resolve a verifier's abstentions by a fresh random bit, at a polynomial point. -/
def ClosedUnderCoinFill (E : VerifierModel) : Prop :=
  ∀ M (a k : ℕ), E.Eff M → E.Eff (boolVerifier (coinFill M (polyLen a k)))

/-- `ClosedUnderCoinFill E` unfolds to closure of `E.Eff` under `coinFill` at polynomial
points. -/
theorem closedUnderCoinFill_iff (E : VerifierModel) :
    ClosedUnderCoinFill E ↔
      ∀ M (a k : ℕ), E.Eff M → E.Eff (boolVerifier (coinFill M (polyLen a k))) := Iff.rfl

/-! ### Closure of GapP -/

variable {E : VerifierModel}

/-- GapP is closed under negation. [FR99, §2]

**Proof sketch.** Use `negVerifier M` on the same schedule (`gap_negVerifier`). -/
theorem IsGapP.neg (hN : ClosedUnderGapNeg E) {f : List Bool → ℤ} (hf : IsGapP E f) :
    IsGapP E fun x => - f x := by
  sorry

/-- GapP is closed under sums. [FR99, §2]

**Proof sketch.** Let `f`, `g` have verifiers on schedules `polyLen a₁ k₁`, `polyLen a₂ k₂`. Pad
both to the common schedule `q = polyLen (a₁ + a₂) (max k₁ k₂)`, which dominates both
(`gap_padVerifier`, `ClosedUnderPad` with `c = 0`). Their `sumVerifier` has gap `f + g` on length
`q n + 1` (`gap_sumVerifier`, `ClosedUnderGapSum`). Pad once more, with `c = 1`, to the schedule
`polyLen (a₁ + a₂ + 1) (max k₁ k₂) ≥ q + 1`. -/
theorem IsGapP.add (hP : ClosedUnderPad E) (hS : ClosedUnderGapSum E) {f g : List Bool → ℤ}
    (hf : IsGapP E f) (hg : IsGapP E g) : IsGapP E fun x => f x + g x := by
  sorry

/-- GapP is closed under products. [FR99, §2]

**Proof sketch.** Pad both verifiers to a common schedule `q = polyLen A K` as in `IsGapP.add`.
Their `prodVerifier` split at `q` has gap `f · g` on length `q n + q n = polyLen (2A) K n`
(`gap_prodVerifier`, `ClosedUnderGapProd`). -/
theorem IsGapP.mul (hP : ClosedUnderPad E) (hM : ClosedUnderGapProd E) {f g : List Bool → ℤ}
    (hf : IsGapP E f) (hg : IsGapP E g) : IsGapP E fun x => f x * g x := by
  sorry

/-- The constant function `1` is in GapP.

**Proof sketch.** `constVerifier true` on the schedule `polyLen 0 0 = 0` (`gap_constVerifier`). -/
theorem isGapP_one (hK : HasConstVerifiers E) : IsGapP E fun _ => 1 := by
  sorry

/-- The constant function `-1` is in GapP.

**Proof sketch.** `constVerifier false` on the schedule `polyLen 0 0 = 0`
(`gap_constVerifier`). -/
theorem isGapP_neg_one (hK : HasConstVerifiers E) : IsGapP E fun _ => -1 := by
  sorry

/-! ### PP through gap functions -/

/-- `L ∈ PP` iff membership in `L` is the sign of a gap function: `x ∈ L ↔ f x > 0`.
[Wat08, §IV.5]

**Proof sketch.** (⇒) A `PP` verifier `M` is a verifier that never abstains, and
`gap (boolVerifier M)` is positive exactly when `Pr[accept] > 1/2` (`gap_boolVerifier`).
(⇐) For a gap verifier `M` on schedule `polyLen a k`, `coinFill M (polyLen a k)` is a Boolean
verifier (`ClosedUnderCoinFill`) whose acceptance probability on the schedule
`polyLen (a + 1) k ≥ polyLen a k + 1` is `1/2 + f x / 2^(…)` (`randProb_coinFill`), which exceeds
`1/2` exactly when `f x > 0`. -/
theorem inPP_iff_exists_isGapP (hC : ClosedUnderCoinFill E) (L : Language Bool) :
    InPP E L ↔ ∃ f : List Bool → ℤ, IsGapP E f ∧ ∀ x, x ∈ L ↔ 0 < f x := by
  sorry

end Counting
