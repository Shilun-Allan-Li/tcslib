/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.Minimax
import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle
import TCSlib.CommunicationComplexity.DeterministicCC.Helper
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Discrepancy

## Main definitions

- `discrepancy`: the discrepancy of a Boolean function on a set `S ⊆ X × Y` with respect
  to a finite distribution on `X × Y`

## Main results

- `discrepancy_eq_prob_false_sub_prob_true`: the discrepancy of `g` on `S` is the mass
  of the `false` part of `S` minus the mass of the `true` part
- `Deterministic.Protocol.one_sub_two_distributionalError_le_two_pow_mul`: the core
  discrepancy bound `1 − 2e ≤ 2^c · γ` for a deterministic protocol of complexity `c`
  and distributional error `e`
- `Deterministic.Protocol.logb_le_complexity_of_distributionalError`: the same bound in
  logarithmic form, `log₂((1 − 2e)/γ) ≤ c`
- `PublicCoin.lt_communicationComplexity_of_discrepancy_bound`: discrepancy method lower
  bound for public-coin communication complexity: if every combinatorial rectangle has
  small discrepancy, then the communication complexity is large

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory
open scoped BigOperators

variable {X Y : Type*}

/-- The discrepancy of a Boolean function `g` on a subset `S ⊆ X × Y`
with respect to a distribution `μ` on `X × Y`: the expectation under `μ`
of the indicator of `S` times the `±1` sign of `g`, i.e. the `μ`-mass of the
`false` part of `S` minus the `μ`-mass of its `true` part.
[RY20, Ch. 5, Definition (Discrepancy)]. Deviation: taken relative to an arbitrary
finite distribution `μ` on `X × Y` (RY20 takes the expectation over "a random input x",
uniform in its applications such as Thm 5.6), and defined as
the signed expectation, without RY20's absolute value; the sign convention `boolSign`
(`false ↦ 1`, `true ↦ −1`) agrees with RY20's `(−1)^{g(x)}`. The lower bounds below use
`|discrepancy g R|`. -/
noncomputable def discrepancy
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool)
    (S : Set (X × Y)) : ℝ := by
  classical
  exact ∫ xy : X × Y,
    (if xy ∈ S then (1 : ℝ) else 0) * boolSign (g xy.1 xy.2)

/-- Rewrite the signed indicator used in discrepancy as the difference
of the indicators of the `false` and `true` parts of `g` on `S`. -/
private lemma discrepancy_integrand_eq
    (g : X → Y → Bool) (S : Set (X × Y)) (xy : X × Y) :
    Set.indicator S (fun _ : X × Y => (1 : ℝ)) xy * boolSign (g xy.1 xy.2) =
      Set.indicator {xy : X × Y | xy ∈ S ∧ g xy.1 xy.2 = false}
        (fun _ : X × Y => (1 : ℝ)) xy -
      Set.indicator {xy : X × Y | xy ∈ S ∧ g xy.1 xy.2 = true}
        (fun _ : X × Y => (1 : ℝ)) xy := by
  classical
  by_cases hS : xy ∈ S <;> cases hg : g xy.1 xy.2 <;> simp [boolSign, hS, hg]

/-- The discrepancy of `g` on `S` equals the probability mass of the `false` part of `g`
on `S` minus the probability mass of the `true` part of `g` on `S`.

**Proof sketch.** Step 1: rewrite the integrand of `discrepancy` as the indicator of `S`
times the sign of `g`, and then (pointwise, by `discrepancy_integrand_eq`) as the
difference of the indicators of the `false` part and the `true` part of `S`. Step 2: by
linearity of the integral on a finite space, the integral of the difference is the
difference of the two indicator integrals, and each indicator integral is the
probability of the corresponding set. -/
theorem discrepancy_eq_prob_false_sub_prob_true
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool)
    (S : Set (X × Y)) :
    discrepancy g S =
      volume.real {xy : X × Y | xy ∈ S ∧ g xy.1 xy.2 = false} -
      volume.real {xy : X × Y | xy ∈ S ∧ g xy.1 xy.2 = true} := by
  classical
  let SFalse : Set (X × Y) := {xy : X × Y | xy ∈ S ∧ g xy.1 xy.2 = false}
  let STrue : Set (X × Y) := {xy : X × Y | xy ∈ S ∧ g xy.1 xy.2 = true}
  -- Step 1: rewrite discrepancy as a difference of two indicator integrals.
  rw [discrepancy]
  have h_indicator :
      (fun xy : X × Y => (if xy ∈ S then (1 : ℝ) else 0) * boolSign (g xy.1 xy.2)) =
      fun xy : X × Y =>
        Set.indicator S 1 xy * boolSign (g xy.1 xy.2) := by
    ext xy
    simp [Set.indicator_apply]
  rw [h_indicator]
  have h_integrand :
      (fun xy : X × Y =>
        Set.indicator S 1 xy * boolSign (g xy.1 xy.2)) =
      fun xy : X × Y =>
        Set.indicator SFalse 1 xy -
          Set.indicator STrue 1 xy := by
    ext xy
    simpa [SFalse, STrue] using discrepancy_integrand_eq g S xy
  rw [h_integrand]
  -- Step 2: use linearity of the integral and identify each indicator integral
  -- with the corresponding probability.
  rw [integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  rw [← FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
      (Ω := X × Y) SFalse]
  rw [← FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
      (Ω := X × Y) STrue]

namespace Deterministic

namespace Protocol

/-- A uniform bound `γ` on the absolute discrepancy of all rectangles is nonnegative
(apply the bound to the full rectangle `X × Y`). -/
private lemma nonneg_of_discrepancy_bound
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool) (γ : ℝ)
    (hdisc : ∀ R : Set (X × Y), Rectangle.IsRectangle R → |discrepancy g R| ≤ γ) :
    0 ≤ γ := by
  have huniv :=
    hdisc Set.univ ⟨Set.univ, Set.univ, by
      ext xy
      simp⟩
  exact le_trans (abs_nonneg _) huniv

/-- The sign attached to a rectangle in the leaf partition of a Boolean protocol:
it is `1` when the protocol outputs `false` on that rectangle, and `-1` otherwise. -/
private noncomputable def rectangleSign
    (p : Protocol X Y Bool) (R : Set (X × Y)) : ℝ := by
  classical
  exact if ∀ xy ∈ R, p.run xy.1 xy.2 = false then 1 else -1

/-- The rectangle sign has absolute value `1`. -/
private lemma rectangleSign_abs
    (p : Protocol X Y Bool) (R : Set (X × Y)) :
    |rectangleSign p R| = 1 := by
  classical
  rw [rectangleSign]
  split_ifs <;> norm_num

/-- On a leaf rectangle `R` of `p`, the rectangle sign of `R` equals the `±1` sign of the
protocol's output at any point of `R` (the output is constant on leaf rectangles).

**Proof sketch.** Case on whether the protocol outputs `false` at every point of `R`. If so,
the rectangle sign is `1` and so is the sign of the output at `xy`. Otherwise the output is
constant on the leaf rectangle (`leafRectangles_mono`), so it cannot be `false` at `xy` (it
would then be `false` on all of `R`); hence it is `true` and both sides equal `-1`. -/
private lemma rectangleSign_eq_boolSign
    (p : Protocol X Y Bool)
    {R : Set (X × Y)} (hR : R ∈ p.leafRectangles)
    {xy : X × Y} (hxy : xy ∈ R) :
    rectangleSign p R = boolSign (p.run xy.1 xy.2) := by
  classical
  by_cases hfalse : ∀ z ∈ R, p.run z.1 z.2 = false
  · rw [rectangleSign, if_pos hfalse]
    simp [boolSign, hfalse xy hxy]
  · have hmono := leafRectangles_mono p p.run rfl R hR
    have htrue : p.run xy.1 xy.2 = true := by
      cases hrun : p.run xy.1 xy.2 with
      | false =>
          exfalso
          apply hfalse
          intro z hz
          rw [hmono z.1 xy.1 z.2 xy.2 hz hxy, hrun]
      | true =>
          rfl
    · rw [rectangleSign, if_neg hfalse]
      simp [boolSign, htrue]

/-- A finite enumeration of the leaf rectangles of a protocol. -/
private noncomputable def leafRectanglesFinset
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool) : Finset (Set (X × Y)) :=
  (Set.toFinite p.leafRectangles).toFinset

/-- Membership in the finite enumeration of leaf rectangles is membership in the set of
leaf rectangles. -/
private lemma mem_leafRectanglesFinset
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool) (R : Set (X × Y)) :
    R ∈ leafRectanglesFinset p ↔ R ∈ p.leafRectangles := by
  classical
  simpa [leafRectanglesFinset] using ((Set.toFinite p.leafRectangles).mem_toFinset (a := R))

open Classical in
/-- Summing, over the leaf rectangles `R` of `p`, the indicator of `R` weighted by the
rectangle sign of `R` gives the `±1` sign of the protocol's output at every point: the
leaf rectangles partition `X × Y`, so exactly one term is nonzero. -/
private lemma sum_indicator_leafRectangles_eq
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool) (xy : X × Y) :
    Finset.sum (leafRectanglesFinset p)
      (fun R => Set.indicator R (fun _ => rectangleSign p R) xy) =
      boolSign (p.run xy.1 xy.2) := by
  classical
  let hPart := leafRectangles_isMonoPartition p p.run rfl
  obtain ⟨R, hR, hxyR⟩ := Rectangle.monoPartition_point_mem hPart xy
  have hR' : R ∈ leafRectanglesFinset p := by
    exact (mem_leafRectanglesFinset p R).2 hR
  rw [Finset.sum_eq_single_of_mem R hR']
  · simp [hxyR, rectangleSign_eq_boolSign p hR hxyR]
  · intro S hS hSR
    have hxyS : xy ∉ S := by
      intro hxyS
      have hEq :=
        Rectangle.monoPartition_part_unique hPart hR ((mem_leafRectanglesFinset p S).1 hS) hxyR hxyS
      exact hSR hEq.symm
    simp [hxyS]

/-- The expected product of the `±1` signs of the protocol's output and of `g` (the
signed bias, or correlation, of `p` with `g` under `μ`) equals `1 − 2e`, where `e` is the
distributional error of `p` with respect to `g`: pointwise the product is `1 − 2·1[p
errs]`, and the integral of the error indicator is `e`.

**Proof sketch.** Let `E` be the set of inputs on which `p` and `g` disagree. (1) Pointwise,
the product of the two signs equals `1 − 2·1_E` (`boolSign_mul_boolSign_eq_sub_two_indicator`).
(2) Integrate: on a finite space both terms are integrable, the constant `1` integrates to
`1` under a probability measure, and the integral of the indicator of `E` is the measure of
`E`, which is by definition the distributional error. -/
private lemma signedBias_eq_one_sub_two_distributionalError
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool)
    (g : X → Y → Bool) :
    ∫ xy : X × Y, boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2) =
      1 - 2 * p.distributionalError μ g := by
  classical
  let Err : Set (X × Y) := {xy : X × Y | p.run xy.1 xy.2 ≠ g xy.1 xy.2}
  have hpoint :
      (fun xy : X × Y => boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2)) =
      fun xy : X × Y => (1 : ℝ) - 2 * Set.indicator Err 1 xy := by
    ext xy
    by_cases hxy : p.run xy.1 xy.2 ≠ g xy.1 xy.2
    · simp [Err, hxy, boolSign_mul_boolSign_eq_sub_two_indicator]
    · simp [Err, hxy, boolSign_mul_boolSign_eq_sub_two_indicator]
  rw [hpoint]
  rw [integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  rw [MeasureTheory.integral_const]
  rw [MeasureTheory.integral_const_mul]
  rw [← FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
    (Ω := X × Y) Err]
  rw [measureReal_univ_eq_one]
  simp [Deterministic.Protocol.distributionalError, Measure.real, Err]

/-- The signed bias of `p` with `g` equals the sum, over the leaf rectangles `R` of `p`,
of the rectangle sign of `R` times the discrepancy of `g` on `R`.

**Proof sketch.** Pointwise, replace the sign of the protocol's output by the sum of
signed rectangle indicators (`sum_indicator_leafRectangles_eq`) and distribute the sign
of `g` over the sum. Then exchange the finite sum with the integral and identify each
term with `rectangleSign p R` times the integral defining `discrepancy g R`. -/
private lemma signedBias_eq_sum_rectangles
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool)
    (g : X → Y → Bool) :
    ∫ xy : X × Y, boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2) =
      Finset.sum (leafRectanglesFinset p) (fun R => rectangleSign p R * discrepancy g R) := by
  classical
  have hpoint :
      (fun xy : X × Y => boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2)) =
      fun xy : X × Y =>
        Finset.sum (leafRectanglesFinset p)
          (fun R => Set.indicator R (fun _ => rectangleSign p R) xy * boolSign (g xy.1 xy.2)) := by
    ext xy
    calc
      boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2) =
          (Finset.sum (leafRectanglesFinset p)
            (fun R => Set.indicator R (fun _ => rectangleSign p R) xy)) *
            boolSign (g xy.1 xy.2) := by
              rw [sum_indicator_leafRectangles_eq p xy]
      _ = Finset.sum (leafRectanglesFinset p)
            (fun R => Set.indicator R (fun _ => rectangleSign p R) xy *
              boolSign (g xy.1 xy.2)) := by
              rw [Finset.sum_mul]
  rw [hpoint, MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro R hR
    have hterm :
        (fun xy : X × Y =>
          Set.indicator R (fun _ => rectangleSign p R) xy * boolSign (g xy.1 xy.2)) =
        fun xy : X × Y =>
          rectangleSign p R * ((if xy ∈ R then (1 : ℝ) else 0) * boolSign (g xy.1 xy.2)) := by
      ext xy
      by_cases hxy : xy ∈ R <;> simp [hxy, mul_comm]
    rw [hterm, MeasureTheory.integral_const_mul, discrepancy]
  · intro R hR
    exact Integrable.of_finite

/-- Core discrepancy bound: if every combinatorial rectangle has absolute discrepancy at
most `γ` (with respect to `μ`), then every deterministic Boolean protocol `p` of
complexity `c` and distributional error `e` (with respect to `μ` and `g`) satisfies
`1 − 2e ≤ 2^c · γ`. [RY20, Thm 5.2 proof] (`1 − 2e ≤ 2^c · γ`).

**Proof sketch.** Step 1: `γ ≥ 0`, and each leaf rectangle `R` of `p` is a rectangle,
so `|rectangleSign p R · disc(g, R)| ≤ γ`. Step 2: by the triangle inequality, the sum
over the leaf rectangles of these signed discrepancies has absolute value at most
`(number of leaf rectangles) · γ`. Step 3: a protocol of complexity `c` has at most
`2^c` leaf rectangles. Step 4: the signed bias of `p` with `g` equals that sum
(`signedBias_eq_sum_rectangles`), hence is bounded by `2^c · γ` in absolute value.
Step 5: the signed bias equals `1 − 2e` (`signedBias_eq_one_sub_two_distributionalError`),
and `1 − 2e ≤ |1 − 2e|`. -/
theorem one_sub_two_distributionalError_le_two_pow_mul
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool) (γ : ℝ)
    (p : Protocol X Y Bool)
    (hdisc : ∀ R : Set (X × Y), Rectangle.IsRectangle R → |discrepancy g R| ≤ γ) :
    1 - 2 * p.distributionalError μ g ≤ (2 : ℝ) ^ p.complexity * γ := by
  -- Step 1: γ ≥ 0 and each leaf rectangle's signed discrepancy is at most γ
  have hγ_nonneg := nonneg_of_discrepancy_bound (μ := μ) g γ hdisc
  have hrect :
      ∀ R ∈ leafRectanglesFinset p, |rectangleSign p R * discrepancy g R| ≤ γ := by
    intro R hR
    have hRrect :
        Rectangle.IsRectangle R :=
      Deterministic.Protocol.leafRectangles_isRectangle p R
        ((mem_leafRectanglesFinset p R).1 hR)
    calc
      |rectangleSign p R * discrepancy g R|
          = |rectangleSign p R| * |discrepancy g R| := by rw [abs_mul]
      _ = |discrepancy g R| := by rw [rectangleSign_abs, one_mul]
      _ ≤ γ := hdisc R hRrect
  -- Step 2: triangle inequality over the leaf rectangles
  have hsum :
      |Finset.sum (leafRectanglesFinset p) (fun R => rectangleSign p R * discrepancy g R)|
        ≤ ((leafRectanglesFinset p).card : ℝ) * γ := by
    calc
      |Finset.sum (leafRectanglesFinset p) (fun R => rectangleSign p R * discrepancy g R)|
          ≤ Finset.sum (leafRectanglesFinset p)
              (fun R => |rectangleSign p R * discrepancy g R|) := by
            simpa using
              (Finset.abs_sum_le_sum_abs (s := leafRectanglesFinset p)
                (f := fun R => rectangleSign p R * discrepancy g R))
      _ ≤ Finset.sum (leafRectanglesFinset p) (fun _ => γ) := by
            exact Finset.sum_le_sum (fun R hR => hrect R hR)
      _ = ((leafRectanglesFinset p).card : ℝ) * γ := by
            simp [nsmul_eq_mul]
  -- Step 3: at most 2^c leaf rectangles
  have hcard :
      ((leafRectanglesFinset p).card : ℝ) ≤ (2 : ℝ) ^ p.complexity := by
    have hcard_nat : (leafRectanglesFinset p).card ≤ 2 ^ p.complexity := by
      rw [show (leafRectanglesFinset p).card = p.leafRectangles.ncard by
        simpa [leafRectanglesFinset] using
          (Set.ncard_eq_toFinset_card p.leafRectangles (Set.toFinite p.leafRectangles)).symm]
      simpa using (Deterministic.Protocol.leafRectangles_card p)
    exact_mod_cast hcard_nat
  -- Step 4: the signed bias is the rectangle sum, hence bounded by 2^c · γ
  have hbias :
      |∫ xy : X × Y, boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2)|
        ≤ (2 : ℝ) ^ p.complexity * γ := by
    rw [signedBias_eq_sum_rectangles]
    exact hsum.trans (mul_le_mul_of_nonneg_right hcard hγ_nonneg)
  -- Step 5: the signed bias is 1 − 2e
  have habs :
      |1 - 2 * p.distributionalError μ g| ≤ (2 : ℝ) ^ p.complexity * γ := by
    simpa [signedBias_eq_one_sub_two_distributionalError] using hbias
  exact (le_abs_self _).trans habs

/-- Discrepancy bound in logarithmic form: if every rectangle has absolute discrepancy
at most `γ > 0` and a deterministic Boolean protocol `p` has distributional error `e`
with `1 − 2e > 0`, then `log₂((1 − 2e) / γ) ≤ complexity of p`. [RY20, Thm 5.2]
(distributional form: `log₂((1−2e)/γ) ≤ c`). Follows from
`one_sub_two_distributionalError_le_two_pow_mul` by dividing by `γ` and taking
logarithms. -/
theorem logb_le_complexity_of_distributionalError
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool) (γ : ℝ)
    (p : Protocol X Y Bool)
    (hdisc : ∀ R : Set (X × Y), Rectangle.IsRectangle R → |discrepancy g R| ≤ γ)
    (hγ : 0 < γ)
    (herr : 0 < 1 - 2 * p.distributionalError μ g) :
    Real.logb 2 ((1 - 2 * p.distributionalError μ g) / γ) ≤ p.complexity := by
  have hmain := one_sub_two_distributionalError_le_two_pow_mul (μ := μ) g γ p hdisc
  have hdiv :
      (1 - 2 * p.distributionalError μ g) / γ ≤ (2 : ℝ) ^ p.complexity := by
    rw [div_le_iff₀ hγ]
    exact hmain
  have hpos : 0 < (1 - 2 * p.distributionalError μ g) / γ := by
    positivity
  rw [Real.logb_le_iff_le_rpow (b := (2 : ℝ)) (hb := by norm_num) hpos]
  simpa [Real.rpow_natCast] using hdiv

end Protocol

end Deterministic

namespace PublicCoin

/-- The discrepancy method: if every combinatorial rectangle has absolute discrepancy at
most `γ` with respect to some distribution `μ` on `X × Y`, and `2^n · γ < 1 − 2ε`, then
the public-coin communication complexity of `g` at error `ε` is greater than `n`.
[RY20, Thm 5.2] (via Yao's minimax principle [RY20, Thm 3.3]). Deviation: stated in the
strict form with hypothesis `2^n · γ < 1 − 2ε` and conclusion `n < R^pub_ε(g)`, in place
of RY20's `R^pub_ε(g) ≥ log₂((1 − 2ε)/γ)`.

**Proof sketch.** By `lt_communicationComplexity_of_forall_distributionalError_gt` it suffices
to show that every deterministic protocol `p` of complexity `c ≤ n` has distributional error
`e > ε`. (1) `γ ≥ 0`, because the whole input space is a rectangle whose absolute discrepancy
is at most `γ`. (2) The core bound `one_sub_two_distributionalError_le_two_pow_mul` gives
`1 − 2e ≤ 2^c · γ`. (3) Since `c ≤ n` and `γ ≥ 0`, `2^c · γ ≤ 2^n · γ < 1 − 2ε`, so
`1 − 2e < 1 − 2ε`, i.e. `e > ε`. -/
theorem lt_communicationComplexity_of_discrepancy_bound
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool) (ε γ : ℝ) (n : ℕ)
    (hdisc : ∀ R : Set (X × Y), Rectangle.IsRectangle R → |discrepancy g R| ≤ γ)
    (hbound : (2 : ℝ) ^ n * γ < 1 - 2 * ε) :
    n < communicationComplexity g ε := by
  apply lt_communicationComplexity_of_forall_distributionalError_gt
    (μ := μ) (f := g) (ε := ε) (n := n)
  intro p hp
  -- Step 1: `γ ≥ 0`, since the whole space is a rectangle
  have hγ_nonneg : 0 ≤ γ := by
    have huniv :=
      hdisc Set.univ ⟨Set.univ, Set.univ, by
        ext xy
        simp⟩
    exact le_trans (abs_nonneg _) huniv
  -- Step 2: the core bound `1 − 2e ≤ 2^c · γ`
  have hmain :=
    Deterministic.Protocol.one_sub_two_distributionalError_le_two_pow_mul
      (μ := μ) g γ p hdisc
  -- Step 3: `2^c · γ ≤ 2^n · γ < 1 − 2ε`, hence `e > ε`
  have hpow :
      (2 : ℝ) ^ p.complexity * γ ≤ (2 : ℝ) ^ n * γ := by
    have hpow' : (2 : ℝ) ^ p.complexity ≤ (2 : ℝ) ^ n := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega) hp)
    exact mul_le_mul_of_nonneg_right hpow' hγ_nonneg
  have : 1 - 2 * p.distributionalError μ g < 1 - 2 * ε :=
    lt_of_le_of_lt (hmain.trans hpow) hbound
  linarith

end PublicCoin

end CommunicationComplexity
