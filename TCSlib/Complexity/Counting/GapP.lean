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
`i` of `S` are not integers. This account is for computational-basis inputs to the *unitary
purification* of plan FD-4, in which every discarded wire is retained: erasure gates are excluded,
since a state they produce, such as `I/2` from erasing half of a Bell pair, has no amplitude
vector [Wat08, §§III.2–III.3] (round-2 audit, finding 1). For such a circuit over the gate set of
[Wat08, §III.2] with `h` Hadamard gates, every amplitude is `(1/√2)^h` times a sum of terms in
`{±1, ±i}` (plan FD-10). The real and
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

/-! ### The gap as a signed sum, and splitting random strings -/

/-- The sign of an answer: `1` for accept, `-1` for reject, `0` for abstain. -/
private def sgn : Option Bool → ℤ
  | some true => 1
  | some false => -1
  | none => 0

/-- The sign is the indicator of acceptance minus the indicator of rejection. -/
private theorem sgn_eq (o : Option Bool) :
    sgn o = (if o = some true then 1 else 0) - (if o = some false then 1 else 0) := by
  rcases o with _ | _ | _ <;> rfl

/-- The gap is the sum of the signs of the answers over all random strings of the given length. -/
private theorem gap_eq_sum (M : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) :
    gap M m x = ∑ r : Fin m → Bool, sgn (M x (List.ofFn r)) := by
  simp only [sgn_eq, Finset.sum_sub_distrib, Finset.sum_boole, gap_eq]

/-- A sum over strings of length `a + b` is a double sum over a prefix of length `a` and a suffix of
length `b` (`Fin.appendEquiv`). -/
private theorem sum_append {a b : ℕ} (f : List Bool → ℤ) :
    ∑ r : Fin (a + b) → Bool, f (List.ofFn r) =
      ∑ r₁ : Fin a → Bool, ∑ r₂ : Fin b → Bool, f (List.ofFn r₁ ++ List.ofFn r₂) := by
  rw [← (Fin.appendEquiv a b).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r₁ _ => Finset.sum_congr rfl fun r₂ _ => ?_
  rw [← List.ofFn_fin_append]
  rfl

/-- A sum over strings of length `m + 1` splits by the first bit (`Fin.consEquiv`). -/
private theorem sum_cons {m : ℕ} (f : List Bool → ℤ) :
    ∑ r : Fin (m + 1) → Bool, f (List.ofFn r) =
      ∑ t : Fin m → Bool, (f (true :: List.ofFn t) + f (false :: List.ofFn t)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  simp [List.ofFn_succ]

/-- A string is all `false` iff it is the constant `false` string. -/
private theorem all_not_ofFn {b : ℕ} (r : Fin b → Bool) :
    (List.ofFn r).all (fun c => !c) = true ↔ r = fun _ => false := by
  rw [List.all_eq_true]
  constructor
  · intro h; funext i; simpa using h (r i) ((List.mem_ofFn ..).2 ⟨i, rfl⟩)
  · rintro rfl c hc
    obtain ⟨i, rfl⟩ := (List.mem_ofFn ..).1 hc
    rfl

/-- The integer gap of a Boolean verifier (the proof behind `gap_boolVerifier_int`, placed before
`gap_boolVerifier`, which uses it). -/
private theorem gap_boolVerifier_int_aux (M : List Bool → List Bool → Bool) (m : ℕ)
    (x : List Bool) :
    gap (boolVerifier M) m x =
      2 * ((univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = true).card : ℤ) - 2 ^ m := by
  have hsum := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin m → Bool))) (fun r => M x (List.ofFn r) = true)
  rw [card_univ_bitstrings] at hsum
  have hF : (univ.filter fun r : Fin m → Bool => ¬ M x (List.ofFn r) = true) =
      univ.filter fun r : Fin m → Bool => boolVerifier M x (List.ofFn r) = some false := by
    ext r; simp [boolVerifier]
  have hT : (univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = true) =
      univ.filter fun r : Fin m → Bool => boolVerifier M x (List.ofFn r) = some true := by
    ext r; simp [boolVerifier]
  rw [gap_eq, ← hT, ← hF]
  have : ((univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = true).card : ℤ) +
      ((univ.filter fun r : Fin m → Bool => ¬ M x (List.ofFn r) = true).card : ℤ) = 2 ^ m := by
    exact_mod_cast hsum
  linarith

/-- The gap of a Boolean verifier (one that never abstains) is determined by its acceptance
probability: `gap = 2^m · (2 · Pr[accept] - 1)`.

**Proof sketch.** With no abstentions, `#reject = 2^m - #accept`
(`card_univ_bitstrings`, `Finset.filter_card_add_filter_neg_card_eq_card`), so the gap is
`2 · #accept - 2^m`; and `randProb m _ = #accept / 2^m` by definition. -/
theorem gap_boolVerifier (M : List Bool → List Bool → Bool) (m : ℕ) (x : List Bool) :
    (gap (boolVerifier M) m x : ℚ) = 2 ^ m * (2 * randProb m (fun r => M x r = true) - 1) := by
  rw [gap_boolVerifier_int_aux, randProb]
  push_cast
  field_simp

/-- The gap of a Boolean verifier, in integers: twice the number of accepted strings minus `2^m`
(round-1 audit, sanity statement 5).

**Proof sketch.** With no abstentions, `#reject = 2^m - #accept`, as in `gap_boolVerifier`. -/
theorem gap_boolVerifier_int (M : List Bool → List Bool → Bool) (m : ℕ) (x : List Bool) :
    gap (boolVerifier M) m x =
      2 * ((univ.filter fun r : Fin m → Bool => M x (List.ofFn r) = true).card : ℤ) - 2 ^ m :=
  gap_boolVerifier_int_aux M m x

/-- A gap on length `m` is at most `2^m` in absolute value (round-1 audit, sanity statement 5).

**Proof sketch.** The gap is the sum over the `2^m` strings of the answer's sign, `1`, `-1` or `0`
(`gap_eq_sum`). Its absolute value is at most the sum of the absolute values of the signs, each at
most `1`. -/
theorem abs_gap_le (M : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) :
    |gap M m x| ≤ 2 ^ m := by
  rw [gap_eq_sum]
  calc |∑ r : Fin m → Bool, sgn (M x (List.ofFn r))|
      ≤ ∑ r : Fin m → Bool, |sgn (M x (List.ofFn r))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin m → Bool, (1 : ℤ) := Finset.sum_le_sum fun r _ => by
        rcases M x (List.ofFn r) with _ | _ | _ <;> simp [sgn]
    _ = 2 ^ m := by simp

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
shorter strings, abstentions use the `false` default, and the formula need not hold (round-1
audit, finding 5; round-2 audit, finding 3). -/
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

**Proof sketch.** In the gap as a sum of signs (`gap_eq_sum`), negating the verifier negates every
sign (accept and reject swap, abstention stays `0`). -/
theorem gap_negVerifier (M : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) :
    gap (negVerifier M) m x = - gap M m x := by
  rw [gap_eq_sum, gap_eq_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [negVerifier_eq]
  rcases M x (List.ofFn r) with _ | _ | _ <;> rfl

/-- Padding does not change the gap: on any length `m ≥ p |x|`, `padVerifier M p` has the gap of
`M` on length `p |x|`.

**Proof sketch.** Split each string of length `m` as `r₁ ++ r₂` with `|r₁| = p |x|`
(`Fin.append`-style bijection `(Fin m → Bool) ≃ (Fin (p |x|) → Bool) × (Fin (m - p |x|) → Bool)`).
Only `r₂ = 0…0` gives a non-abstaining answer, namely `M x r₁`, so both counts equal those of `M`
on length `p |x|`. -/
theorem gap_padVerifier (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) {m : ℕ}
    (x : List Bool) (h : p x.length ≤ m) :
    gap (padVerifier M p) m x = gap M (p x.length) x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [gap_eq_sum, sum_append (fun l => sgn (padVerifier M p x l)), gap_eq_sum]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  rw [Finset.sum_eq_single (fun _ => false)]
  · rw [padVerifier_eq, List.drop_left' (List.length_ofFn), List.take_left' (List.length_ofFn),
      if_pos ((all_not_ofFn _).2 rfl)]
  · intro r₂ _ hr
    rw [padVerifier_eq, List.drop_left' (List.length_ofFn),
      if_neg (fun h => hr ((all_not_ofFn r₂).1 h))]; rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The sum verifier adds gaps: on length `m + 1`, its gap is the gap of `M₁` plus the gap of
`M₂`, both on length `m`.

**Proof sketch.** Split strings of length `m + 1` by their first bit (`Fin.consEquiv`). Strings
starting with `true` contribute `M₁`'s counts on the tail and strings starting with `false`
contribute `M₂`'s. -/
theorem gap_sumVerifier (M₁ M₂ : List Bool → List Bool → Option Bool) (m : ℕ) (x : List Bool) :
    gap (sumVerifier M₁ M₂) (m + 1) x = gap M₁ m x + gap M₂ m x := by
  rw [gap_eq_sum, sum_cons (fun l => sgn (sumVerifier M₁ M₂ x l)), Finset.sum_add_distrib,
    gap_eq_sum, gap_eq_sum]
  rfl

/-- The product verifier multiplies gaps: on length `p |x| + m`, its gap is the gap of `M₁` on
length `p |x|` times the gap of `M₂` on length `m`.

**Proof sketch.** Split strings as `r₁ ++ r₂` as in `gap_padVerifier`. The answer is accept when
the two answers agree and reject when they differ, so with `s(true) = 1`, `s(false) = -1`,
`s(none) = 0`, the gap is `∑_{r₁, r₂} s(M₁ r₁) · s(M₂ r₂) = (∑ s(M₁ r₁)) · (∑ s(M₂ r₂))`. -/
theorem gap_prodVerifier (M₁ M₂ : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) (m : ℕ)
    (x : List Bool) :
    gap (prodVerifier M₁ M₂ p) (p x.length + m) x = gap M₁ (p x.length) x * gap M₂ m x := by
  rw [gap_eq_sum, sum_append (fun l => sgn (prodVerifier M₁ M₂ p x l)), gap_eq_sum,
    gap_eq_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun r₁ _ => Finset.sum_congr rfl fun r₂ _ => ?_
  rw [prodVerifier_eq, List.take_left' (List.length_ofFn), List.drop_left' (List.length_ofFn)]
  rcases M₁ x (List.ofFn r₁) with _ | _ | _ <;> rcases M₂ x (List.ofFn r₂) with _ | _ | _ <;> rfl

/-- The constant verifier with answer `b` has gap `1` if `b = true` and `-1` if `b = false`, on
every length.

**Proof sketch.** Exactly one string of each length is all-`false`, and it is the only string on
which the verifier answers. -/
theorem gap_constVerifier (b : Bool) (m : ℕ) (x : List Bool) :
    gap (constVerifier b) m x = if b then 1 else -1 := by
  rw [gap_eq_sum, Finset.sum_eq_single (fun _ => false)]
  · rw [constVerifier_eq, if_pos ((all_not_ofFn _).2 rfl)]; cases b <;> rfl
  · intro r _ hr; rw [constVerifier_eq, if_neg (fun h => hr ((all_not_ofFn r).1 h))]; rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The gap of `coinFill M p` on length `p |x| + (d + 1)` is `2^(d + 1)` times the gap of `M` on
length `p |x|`: an abstaining string contributes `+1` and `-1` for the two coin values. -/
private theorem gap_coinFill (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) (d : ℕ)
    (x : List Bool) :
    gap (boolVerifier (coinFill M p)) (p x.length + (d + 1)) x =
      2 ^ (d + 1) * gap M (p x.length) x := by
  rw [gap_eq_sum, sum_append (fun l => sgn (boolVerifier (coinFill M p) x l)), gap_eq_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  rw [sum_cons (fun l => sgn (boolVerifier (coinFill M p) x (List.ofFn r₁ ++ l)))]
  simp only [boolVerifier, coinFill_eq, List.take_left' (List.length_ofFn),
    List.drop_left' (List.length_ofFn), List.headD_cons, Finset.sum_const, card_univ_bitstrings,
    nsmul_eq_mul]
  push_cast
  rcases M x (List.ofFn r₁) with _ | _ | _ <;> simp [sgn] <;> ring

/-- The acceptance probability of `coinFill M p` on any length `m ≥ p |x| + 1` is
`1/2 + gap / 2^(p |x| + 1)`, where `gap` is the gap of `M` on length `p |x|`. In particular it is
above `1/2` exactly when the gap is positive.

**Proof sketch.** Write `m = p |x| + (d + 1)`. As a Boolean verifier, `coinFill M p` has gap
`2^(d + 1)` times `M`'s gap on length `p |x|` (`gap_coinFill`): splitting a string as prefix, coin
bit and rest, a string `M` accepts or rejects keeps its sign for both coins, an abstaining string
contributes `+1` and `-1`, and the rest repeats each case `2^d` times. Then `gap_boolVerifier`
relates that gap to the acceptance probability, `gap = 2^m (2 Pr - 1)`; solving for `Pr` gives
`1/2 + gap / 2^(p |x| + 1)`. -/
theorem randProb_coinFill (M : List Bool → List Bool → Option Bool) (p : ℕ → ℕ) {m : ℕ}
    (x : List Bool) (h : p x.length + 1 ≤ m) :
    randProb m (fun r => coinFill M p x r = true) =
      1/2 + (gap M (p x.length) x : ℚ) / 2 ^ (p x.length + 1) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  have hm : m = p x.length + (d + 1) := by omega
  subst hm
  have h1 := gap_boolVerifier (coinFill M p) (p x.length + (d + 1)) x
  rw [gap_coinFill] at h1
  push_cast at h1
  have h4 : (gap M (p x.length) x : ℚ) =
      2 ^ p x.length *
        (2 * randProb (p x.length + (d + 1)) (fun r => coinFill M p x r = true) - 1) := by
    apply mul_left_cancel₀ (pow_ne_zero (d + 1) (two_ne_zero : (2 : ℚ) ≠ 0))
    rw [h1]
    ring
  rw [h4]
  field_simp
  ring

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
  obtain ⟨M, a, k, hM, hf⟩ := hf
  exact ⟨negVerifier M, a, k, hN M hM, fun x => by rw [gap_negVerifier, ← hf x]⟩

/-- A schedule is dominated by the schedule with the summed coefficient and the larger degree. -/
private theorem polyLen_le_polyLen (a₁ k₁ a₂ k₂ n : ℕ) :
    polyLen a₁ k₁ n ≤ polyLen (a₁ + a₂) (max k₁ k₂) n := by
  simp only [polyLen]
  exact Nat.mul_le_mul (Nat.le_add_right _ _)
    (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _))

/-- Raising the coefficient by one adds at least one bit. -/
private theorem polyLen_succ_le (a k n : ℕ) : polyLen a k n + 1 ≤ polyLen (a + 1) k n := by
  simp only [polyLen, add_mul, one_mul]
  exact Nat.add_le_add_left (Nat.one_le_pow _ _ (Nat.succ_pos _)) _

/-- Two gap functions have witnesses on one common schedule `polyLen A K`: pad each witness to
`polyLen (a₁ + a₂) (max k₁ k₂)`, which dominates both schedules. Shared by `IsGapP.add` and
`IsGapP.mul`. -/
private theorem IsGapP.common_schedule (hP : ClosedUnderPad E) {f g : List Bool → ℤ}
    (hf : IsGapP E f) (hg : IsGapP E g) :
    ∃ (M₁ M₂ : List Bool → List Bool → Option Bool) (A K : ℕ), E.Eff M₁ ∧ E.Eff M₂ ∧
      ∀ x, f x = gap M₁ (polyLen A K x.length) x ∧ g x = gap M₂ (polyLen A K x.length) x := by
  obtain ⟨M₁, a₁, k₁, h₁, hf⟩ := hf
  obtain ⟨M₂, a₂, k₂, h₂, hg⟩ := hg
  refine ⟨padVerifier M₁ fun n => polyLen a₁ k₁ n + 0, padVerifier M₂ fun n => polyLen a₂ k₂ n + 0,
    a₁ + a₂, max k₁ k₂, hP M₁ a₁ k₁ 0 h₁, hP M₂ a₂ k₂ 0 h₂, fun x => ⟨?_, ?_⟩⟩
  · have b : polyLen a₁ k₁ x.length + 0 ≤ polyLen (a₁ + a₂) (max k₁ k₂) x.length := by
      simpa using polyLen_le_polyLen a₁ k₁ a₂ k₂ x.length
    rw [gap_padVerifier _ _ x b, Nat.add_zero]
    exact hf x
  · have b : polyLen a₂ k₂ x.length + 0 ≤ polyLen (a₁ + a₂) (max k₁ k₂) x.length := by
      have := polyLen_le_polyLen a₂ k₂ a₁ k₁ x.length
      rw [add_comm a₂, max_comm k₂] at this
      simpa using this
    rw [gap_padVerifier _ _ x b, Nat.add_zero]
    exact hg x

/-- GapP is closed under sums. [FR99, §2]

**Proof sketch.** Let `f`, `g` have verifiers on schedules `polyLen a₁ k₁`, `polyLen a₂ k₂`. Pad
both to the common schedule `q = polyLen (a₁ + a₂) (max k₁ k₂)`, which dominates both
(`gap_padVerifier`, `ClosedUnderPad` with `c = 0`). Their `sumVerifier` has gap `f + g` on length
`q n + 1` (`gap_sumVerifier`, `ClosedUnderGapSum`). Pad once more, with `c = 1`, to the schedule
`polyLen (a₁ + a₂ + 1) (max k₁ k₂) ≥ q + 1`. -/
theorem IsGapP.add (hP : ClosedUnderPad E) (hS : ClosedUnderGapSum E) {f g : List Bool → ℤ}
    (hf : IsGapP E f) (hg : IsGapP E g) : IsGapP E fun x => f x + g x := by
  obtain ⟨M₁, M₂, A, K, h₁, h₂, h⟩ := hf.common_schedule hP hg
  refine ⟨padVerifier (sumVerifier M₁ M₂) (fun n => polyLen A K n + 1), A + 1, K,
    hP _ A K 1 (hS _ _ h₁ h₂), fun x => ?_⟩
  rw [gap_padVerifier _ _ x (polyLen_succ_le _ _ _), gap_sumVerifier, ← (h x).1, ← (h x).2]

/-- GapP is closed under products. [FR99, §2]

**Proof sketch.** Pad both verifiers to a common schedule `q = polyLen A K` as in `IsGapP.add`.
Their `prodVerifier` split at `q` has gap `f · g` on length `q n + q n = polyLen (2A) K n`
(`gap_prodVerifier`, `ClosedUnderGapProd`). -/
theorem IsGapP.mul (hP : ClosedUnderPad E) (hM : ClosedUnderGapProd E) {f g : List Bool → ℤ}
    (hf : IsGapP E f) (hg : IsGapP E g) : IsGapP E fun x => f x * g x := by
  obtain ⟨M₁, M₂, A, K, h₁, h₂, h⟩ := hf.common_schedule hP hg
  refine ⟨prodVerifier M₁ M₂ (polyLen A K), 2 * A, K, hM _ _ A K h₁ h₂, fun x => ?_⟩
  have e : polyLen (2 * A) K x.length = polyLen A K x.length + polyLen A K x.length := by
    simp only [polyLen]
    ring
  rw [e, gap_prodVerifier, ← (h x).1, ← (h x).2]

/-- The constant function `1` is in GapP.

**Proof sketch.** `constVerifier true` on the schedule `polyLen 0 0 = 0` (`gap_constVerifier`). -/
theorem isGapP_one (hK : HasConstVerifiers E) : IsGapP E fun _ => 1 :=
  ⟨constVerifier true, 0, 0, hK true, fun x => by rw [gap_constVerifier]; rfl⟩

/-- The constant function `-1` is in GapP.

**Proof sketch.** `constVerifier false` on the schedule `polyLen 0 0 = 0`
(`gap_constVerifier`). -/
theorem isGapP_neg_one (hK : HasConstVerifiers E) : IsGapP E fun _ => -1 :=
  ⟨constVerifier false, 0, 0, hK false, fun x => by rw [gap_constVerifier]; rfl⟩

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
  constructor
  · rintro ⟨M, a, k, hE, h⟩
    refine ⟨fun x => gap (boolVerifier M) (polyLen a k x.length) x,
      ⟨boolVerifier M, a, k, hE, fun _ => rfl⟩, fun x => ?_⟩
    rw [h x]
    have e := gap_boolVerifier M (polyLen a k x.length) x
    have hp : (0 : ℚ) < 2 ^ polyLen a k x.length := by positivity
    constructor
    · intro hlt
      have : (0 : ℚ) < (gap (boolVerifier M) (polyLen a k x.length) x : ℚ) := by
        rw [e]; exact mul_pos hp (by linarith)
      exact_mod_cast this
    · intro hpos
      have : (0 : ℚ) < (gap (boolVerifier M) (polyLen a k x.length) x : ℚ) := by exact_mod_cast hpos
      rw [e] at this
      have := (pos_iff_pos_of_mul_pos this).1 hp
      linarith
  · rintro ⟨f, ⟨M, a, k, hE, hf⟩, hL⟩
    refine ⟨coinFill M (polyLen a k), a + 1, k, hC M a k hE, fun x => ?_⟩
    rw [hL x, randProb_coinFill M (polyLen a k) x (polyLen_succ_le a k x.length), hf x]
    have hp : (0 : ℚ) < 2 ^ (polyLen a k x.length + 1) := by positivity
    constructor
    · intro h
      have : (0 : ℚ) <
          (gap M (polyLen a k x.length) x : ℚ) / 2 ^ (polyLen a k x.length + 1) :=
        div_pos (by exact_mod_cast h) hp
      linarith
    · intro h
      have : (0 : ℚ) <
          (gap M (polyLen a k x.length) x : ℚ) / 2 ^ (polyLen a k x.length + 1) := by
        linarith
      exact_mod_cast (div_pos_iff_of_pos_right hp).1 this

end Counting
