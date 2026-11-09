/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Convexity for biased two-point estimates

## Main definitions

This file introduces no new definitions.

## Main results

* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.symmetric_power_slope_le`:
  a symmetric real-power inequality used in a direct calculus proof of the convexity
  underlying the biased two-point hypercontractive inequality.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.convexOn_symmetric_sqrt_rpow`:
  convexity of the symmetric power sum as a function of the squared perturbation.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.convexOn_biased_power`:
  convexity of the full power expression used in the sharp two-point estimate.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_power_tangent_le`:
  the tangent-line lower bound at an interior squared perturbation.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.tangent_at_bias`:
  the value and slope of the tangent at the normalized bias point.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.normalized_biased_quadratic_le`:
  the sharp weighted inequality for normalized nonnegative two-point inputs.
* `BooleanAnalysis.Hypercontractivity.SharpDiscrete.nonnegative_biased_two_point_le`:
  the same sharp weighted inequality for arbitrary nonnegative input pairs.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercise 10.20(b)–(j), in the setting of Theorem 10.18.
-/

namespace BooleanAnalysis.Hypercontractivity

namespace SharpDiscrete

/--
For `1 < p < 2` and `0 ≤ t < 1`, the difference of the symmetric powers with
exponent `p - 1` is bounded by `(p - 1) * t` times the sum of the symmetric
powers with exponent `p - 2`.

This is a technical reformulation supporting [OD14, Ex. 10.20(j)] and Theorem 10.18.
It supplies a direct calculus alternative to the positive generalized-binomial-series
argument for convexity of
`z ↦ (1 + √z)^p + (1 - √z)^p` on `[0, 1)`. It is an auxiliary inequality,
rather than the final two-point hypercontractive inequality.

**Proof sketch.** Let
`H(x) = (p - 1) * x * ((1 + x)^(p - 2) + (1 - x)^(p - 2))
  - ((1 + x)^(p - 1) - (1 - x)^(p - 1))`.
Then `H(0) = 0`, and differentiation gives
`H'(x) = (p - 1) * (p - 2) * x
  * ((1 + x)^(p - 3) - (1 - x)^(p - 3))`.
On `[0, t]`, both bases are positive. Since `p - 3 < 0` and
`1 - x ≤ 1 + x`, the last difference is nonpositive; the preceding coefficient
is also nonpositive. Thus `H' ≥ 0` on this interval. The derivative criterion
for monotonicity gives `H(t) ≥ H(0) = 0`, which is the desired inequality.
-/
theorem symmetric_power_slope_le (p t : ℝ)
    (hp_one : 1 < p) (hp_two : p < 2)
    (ht_nonneg : 0 ≤ t) (ht_lt_one : t < 1) :
    (1 + t) ^ (p - 1) - (1 - t) ^ (p - 1) ≤
      (p - 1) * t * ((1 + t) ^ (p - 2) + (1 - t) ^ (p - 2)) := by
  let H : ℝ → ℝ := fun x =>
    (p - 1) * x * ((1 + x) ^ (p - 2) + (1 - x) ^ (p - 2)) -
      ((1 + x) ^ (p - 1) - (1 - x) ^ (p - 1))
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc 0 t) :
      HasDerivAt H
        ((p - 1) * (p - 2) * x *
          ((1 + x) ^ (p - 3) - (1 - x) ^ (p - 3))) x := by
    have hxp : 0 < 1 + x := by linarith [hx.1]
    have hxm : 0 < 1 - x := by linarith [hx.2]
    have hplus (r : ℝ) :
        HasDerivAt (fun y : ℝ => (1 + y) ^ r)
          (r * (1 + x) ^ (r - 1)) x := by
      simpa only [one_mul] using
        ((hasDerivAt_id' x).const_add 1).rpow_const
          (p := r) (Or.inl (ne_of_gt hxp))
    have hminus (r : ℝ) :
        HasDerivAt (fun y : ℝ => (1 - y) ^ r)
          (-r * (1 - x) ^ (r - 1)) x := by
      simpa only [neg_one_mul] using
        ((hasDerivAt_id' x).const_sub 1).rpow_const
          (p := r) (Or.inl (ne_of_gt hxm))
    convert
      (((hasDerivAt_id' x).const_mul (p - 1)).mul
        ((hplus (p - 2)).add (hminus (p - 2)))).sub
        ((hplus (p - 1)).sub (hminus (p - 1))) using 1 <;>
      simp only [H, Pi.add_apply, Pi.mul_apply, Pi.sub_apply,
        show p - 2 - 1 = p - 3 by ring,
        show p - 1 - 1 = p - 2 by ring] <;> ring
  have hmono : MonotoneOn H (Set.Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      (continuousOn_of_forall_continuousAt
        (fun x hx => (hderiv x hx).continuousAt))
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x (Set.Ioo_subset_Icc_self hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hpow :
          (1 + x) ^ (p - 3) ≤ (1 - x) ^ (p - 3) :=
        Real.rpow_le_rpow_of_nonpos
          (by linarith [hx.2]) (by linarith [hx.1]) (by linarith)
      have hcoef : (p - 1) * (p - 2) * x ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
          (le_of_lt hx.1)
      exact mul_nonneg_of_nonpos_of_nonpos hcoef (sub_nonpos.mpr hpow)
  have hHt := hmono ⟨le_rfl, ht_nonneg⟩ ⟨ht_nonneg, le_rfl⟩ ht_nonneg
  have hnonneg : 0 ≤ H t := by
    simpa [H, Real.one_rpow] using hHt
  exact sub_nonneg.mp hnonneg

/--
For a real exponent strictly between one and two, the symmetric power function of
the square root is convex on the closed interval `[0, 1]`.

This is a technical supporting result for [OD14, Ex. 10.20(j)] and
[OD14, Thm. 10.18]. It extends the source's interval `[0, 1)` to the closed
interval `[0, 1]` by continuity, so that zero-valued two-point inputs are included.
The proof also uses direct differentiation instead of the source's generalized
binomial series argument.

**Proof sketch.** Continuity of the square root and real powers gives continuity
on `[0, 1]`. For `0 < z < 1`, put `t = √z`. The second derivative is
`p / (4 * t^3)` times
`(p - 1) * t * ((1 + t)^(p - 2) + (1 - t)^(p - 2))
  - ((1 + t)^(p - 1) - (1 - t)^(p - 1))`.
The factor is positive, and the bracket is nonnegative by
`symmetric_power_slope_le`. The second derivative criterion for convexity,
together with endpoint continuity, gives convexity on the closed interval.
-/
theorem convexOn_symmetric_sqrt_rpow (p : Real) (hp_one : 1 < p)
    (hp_two : p < 2) :
    ConvexOn Real (Set.Icc (0 : Real) 1)
      (fun z : Real => (1 + Real.sqrt z) ^ p + (1 - Real.sqrt z) ^ p) := by
  let d1 : ℝ → ℝ := fun z =>
    p / 2 * (((1 + Real.sqrt z) ^ (p - 1) -
      (1 - Real.sqrt z) ^ (p - 1)) / Real.sqrt z)
  let d2 : ℝ → ℝ := fun z =>
    p / (4 * Real.sqrt z ^ 3) *
      ((p - 1) * Real.sqrt z *
        ((1 + Real.sqrt z) ^ (p - 2) + (1 - Real.sqrt z) ^ (p - 2)) -
        ((1 + Real.sqrt z) ^ (p - 1) - (1 - Real.sqrt z) ^ (p - 1)))
  have hp_nonneg : 0 ≤ p := by linarith
  have hexp : p - 1 - 1 = p - 2 := by ring
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := d1) (f'' := d2) (convex_Icc 0 1) ?_ ?_ ?_ ?_
  · -- Continuity includes both endpoints.
    exact (((Real.continuous_rpow_const hp_nonneg).comp
      (continuous_const.add Real.continuous_sqrt)).add
      ((Real.continuous_rpow_const hp_nonneg).comp
        (continuous_const.sub Real.continuous_sqrt))).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have ht_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
    have hs := Real.hasDerivAt_sqrt (ne_of_gt hx.1)
    have hd := ((hs.const_add 1).rpow_const (p := p) (Or.inr hp_one.le)).add
      ((hs.const_sub 1).rpow_const (p := p) (Or.inr hp_one.le))
    convert hd.hasDerivWithinAt using 1 <;>
      simp only [d1, Pi.add_apply] <;>
      field_simp [ne_of_gt ht_pos] <;> ring
  · -- Differentiate the first derivative on the open interval.
    intro x hx
    rw [interior_Icc] at hx
    have ht_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
    have ht_lt : Real.sqrt x < 1 :=
      (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2 (by simpa using hx.2)
    have hplus : 1 + Real.sqrt x ≠ 0 := ne_of_gt (by linarith)
    have hminus : 1 - Real.sqrt x ≠ 0 := ne_of_gt (sub_pos.mpr ht_lt)
    have hs := Real.hasDerivAt_sqrt (ne_of_gt hx.1)
    have hd := (((hs.const_add 1).rpow_const (p := p - 1) (Or.inl hplus)).sub
      ((hs.const_sub 1).rpow_const (p := p - 1) (Or.inl hminus))).div
      hs (ne_of_gt ht_pos)
    convert (hd.const_mul (p / 2)).hasDerivWithinAt using 1 <;>
      simp only [d1, d2, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Pi.div_apply, hexp] <;>
      field_simp [ne_of_gt ht_pos] <;> ring
  · -- The slope bound makes the second derivative nonnegative.
    intro x hx
    rw [interior_Icc] at hx
    have ht_lt : Real.sqrt x < 1 :=
      (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2 (by simpa using hx.2)
    have hslope := symmetric_power_slope_le p (Real.sqrt x)
      hp_one hp_two (Real.sqrt_nonneg x) ht_lt
    dsimp [d2]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hslope)

/-- For `1 < p < 2`, the function
`z ↦ ((1 + √z)^p + (1 - √z)^p)^(2 / p)` is convex on `[0, 1]`.
This is the convexity ingredient for the sharp biased estimate in
[OD14, Theorem 10.18], as established in [OD14, Ex. 10.20(j)].
The exercise uses `[0, 1)`; continuity extends the conclusion to the closed
endpoint `z = 1`, allowing zero-valued two-point inputs.

**Proof sketch.** The inner sum is convex on the closed interval by
`convexOn_symmetric_sqrt_rpow` and is nonnegative there. Since `1 < p < 2`,
the exponent `2 / p` is greater than one, so the outer power is convex and
increasing on the nonnegative reals. Composing these functions preserves
convexity. -/
theorem convexOn_biased_power (p : ℝ) (hp_one : 1 < p) (hp_two : p < 2) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun z : ℝ => ((1 + Real.sqrt z) ^ p + (1 - Real.sqrt z) ^ p) ^ (2 / p)) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp_one
  have hpower : 1 ≤ 2 / p := (le_div_iff₀ hp_pos).2 (by linarith)
  let g : ℝ → ℝ := fun z => (1 + Real.sqrt z) ^ p + (1 - Real.sqrt z) ^ p
  have hg : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g :=
    convexOn_symmetric_sqrt_rpow p hp_one hp_two
  have hnonneg : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g z := by
    intro z hz
    have hs : Real.sqrt z ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hz.2
    dsimp [g]
    exact add_nonneg (Real.rpow_nonneg (by positivity) p)
      (Real.rpow_nonneg (sub_nonneg.mpr hs) p)
  refine ⟨hg.1, ?_⟩
  intro x hx y hy a b ha hb hab
  change g (a • x + b • y) ^ (2 / p) ≤
    a • (g x ^ (2 / p)) + b • (g y ^ (2 / p))
  exact (Real.rpow_le_rpow (hnonneg _ (hg.1 hx hy ha hb hab))
    (hg.2 hx hy ha hb hab) (le_trans zero_le_one hpower)).trans
      ((convexOn_rpow hpower).2 (hnonneg x hx) (hnonneg y hy) ha hb hab)

/-- For `1 < p < 2` and `0 < t < 1`, the tangent at `t²` to
`z ↦ ((1 + √z)^p + (1 - √z)^p)^(2 / p)` is a lower bound on `[0, 1]`.
This is the tangent-line ingredient in [OD14, Ex. 10.20(i)-(j)] for the
sharp biased estimate [OD14, Theorem 10.18].
Exercise 10.20(i) uses the special value `t = (β - α) / (β + α)`; this
helper allows every `0 < t < 1` and includes the endpoints `z = 0, 1`.

**Proof sketch.** Apply the square-root and power chain rules at `t²`,
using `√(t²) = t` and positivity of the inner sum, to obtain the displayed
derivative. The convexity theorem `convexOn_biased_power` then bounds the
derivative by secant slopes on either side of `t²`. Rearranging gives
the tangent inequality; equality holds when `z = t²`. -/
theorem biased_power_tangent_le (p t z : ℝ)
    (hp_one : 1 < p) (hp_two : p < 2)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    ((1 + t) ^ p + (1 - t) ^ p) ^ (2 / p) +
      ((1 + t) ^ p + (1 - t) ^ p) ^ (2 / p - 1) *
        (((1 + t) ^ (p - 1) - (1 - t) ^ (p - 1)) / t) *
        (z - t ^ 2) ≤
      ((1 + Real.sqrt z) ^ p + (1 - Real.sqrt z) ^ p) ^ (2 / p) := by
  let f : ℝ → ℝ := fun x =>
    ((1 + Real.sqrt x) ^ p + (1 - Real.sqrt x) ^ p) ^ (2 / p)
  let d : ℝ :=
    ((1 + t) ^ p + (1 - t) ^ p) ^ (2 / p - 1) *
      (((1 + t) ^ (p - 1) - (1 - t) ^ (p - 1)) / t)
  have hp : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp_one)
  have htmem : t ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg t, by
      nlinarith [mul_pos ht_pos (sub_pos.mpr ht_lt_one)]⟩
  have hd : HasDerivAt f d (t ^ 2) := by
    have hs : HasDerivAt Real.sqrt (1 / (2 * t)) (t ^ 2) := by
      simpa only [Real.sqrt_sq ht_pos.le] using
        Real.hasDerivAt_sqrt (show t ^ 2 ≠ 0 by positivity)
    have hg :=
      ((hs.const_add 1).rpow_const (p := p) (Or.inr hp_one.le)).add
        ((hs.const_sub 1).rpow_const (p := p) (Or.inr hp_one.le))
    have hsum :
        0 < (1 + Real.sqrt (t ^ 2)) ^ p + (1 - Real.sqrt (t ^ 2)) ^ p := by
      rw [Real.sqrt_sq ht_pos.le]
      exact add_pos
        (Real.rpow_pos_of_pos (by linarith) p)
        (Real.rpow_pos_of_pos (by linarith) p)
    convert hg.rpow_const (p := 2 / p) (Or.inl hsum.ne') using 1 <;>
      simp only [f, d, Pi.add_apply, Real.sqrt_sq ht_pos.le]
    field_simp [hp, ht_pos.ne'] <;> ring
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f :=
    convexOn_biased_power p hp_one hp_two
  suffices f (t ^ 2) + d * (z - t ^ 2) ≤ f z by
    simpa only [f, d, Real.sqrt_sq ht_pos.le] using this
  rcases lt_trichotomy z (t ^ 2) with hzt | hzt | htz
  · have hslope := hconv.slope_le_of_hasDerivAt hz htmem hzt hd
    rw [slope_def_field] at hslope
    nlinarith only [(div_le_iff₀ (sub_pos.mpr hzt)).mp hslope]
  · subst z
    simp
  · have hslope := hconv.le_slope_of_hasDerivAt htmem hz htz hd
    rw [slope_def_field] at hslope
    nlinarith only [(le_div_iff₀ (sub_pos.mpr htz)).mp hslope]
/-- The value and tangent coefficient of the biased power function at
`t²`, where `t = (β - α) / (β + α)`, have explicit formulas.
This is the normalized `α, β` reformulation of the evaluations in
[OD14, Ex. 10.20(g)-(i)], used in [OD14, Theorem 10.18]:
the source takes `α = λ^(1/p)` and `β = (1 - λ)^(1/p)`.

**Proof sketch.** Set `c = 2 / (α + β) > 0`. Then `1 + t = cβ` and
`1 - t = cα`, so multiplicativity of real powers and
`α^p + β^p = 1` give `S = c^p`. The first evaluation follows from
`(c^p)^(2/p) = c²`. For the second, the difference of the two
`(p - 1)` powers contributes `c^(p - 1)`, while
`S^(2/p - 1)` contributes `c^(2 - p)`. Their product is `c`, and
division by `t` gives the stated coefficient. -/
theorem tangent_at_bias (p α β : ℝ) (hp_one : 1 < p) (hp_two : p < 2)
    (hα_pos : 0 < α) (hαβ : α < β) (hnorm : α ^ p + β ^ p = 1) :
    let t := (β - α) / (β + α)
    let S := (1 + t) ^ p + (1 - t) ^ p
    S ^ (2 / p) = 4 / (α + β) ^ 2 ∧
      S ^ (2 / p - 1) *
          (((1 + t) ^ (p - 1) - (1 - t) ^ (p - 1)) / t) =
        2 * (β ^ (p - 1) - α ^ (p - 1)) / (β - α) := by
  let t : ℝ := (β - α) / (β + α)
  let c : ℝ := 2 / (α + β)
  let S : ℝ := (1 + t) ^ p + (1 - t) ^ p
  change S ^ (2 / p) = 4 / (α + β) ^ 2 ∧
    S ^ (2 / p - 1) *
      (((1 + t) ^ (p - 1) - (1 - t) ^ (p - 1)) / t) =
        2 * (β ^ (p - 1) - α ^ (p - 1)) / (β - α)
  have hp : p ≠ 0 := by linarith
  have hβ_pos : 0 < β := lt_trans hα_pos hαβ
  have hs : 0 < α + β := add_pos hα_pos hβ_pos
  have hc : 0 < c := div_pos (by norm_num) hs
  have hpm : 1 + t = c * β ∧ 1 - t = c * α := by
    constructor <;> dsimp [t, c] <;>
      field_simp [ne_of_gt hs, (by linarith : β + α ≠ 0)] <;> ring
  have hS : S = c ^ p := by
    dsimp [S]
    rw [hpm.1, hpm.2, Real.mul_rpow hc.le hβ_pos.le,
      Real.mul_rpow hc.le hα_pos.le, ← mul_add,
      add_comm (β ^ p) (α ^ p), hnorm, mul_one]
  have hscale : (c ^ p) ^ (2 / p - 1) * c ^ (p - 1) = c := by
    rw [← Real.rpow_mul hc.le, ← Real.rpow_add hc,
      show p * (2 / p - 1) + (p - 1) = 1 by
        field_simp [hp] <;> ring,
      Real.rpow_one]
  constructor
  · rw [hS, ← Real.rpow_mul hc.le,
      show p * (2 / p) = (2 : ℝ) by field_simp [hp] <;> ring,
      Real.rpow_two]
    dsimp [c]
    field_simp [ne_of_gt hs] <;> ring
  · rw [hS, hpm.1, hpm.2, Real.mul_rpow hc.le hβ_pos.le,
      Real.mul_rpow hc.le hα_pos.le, ← mul_sub,
      ← mul_div_assoc, ← mul_assoc, hscale]
    dsimp [c, t]
    field_simp [ne_of_gt hs, (by linarith : β + α ≠ 0),
      (by linarith : β - α ≠ 0)] <;> ring

/-- Let `1 < p < 2` and `0 < α < β`, with `α ^ p + β ^ p = 1`.
For every `y ∈ [-1, 1]`, the weighted quadratic expression in the normalized
inputs `(1 + y) / α` and `(1 - y) / β` is bounded by
`((1 + y) ^ p + (1 - y) ^ p) ^ (2 / p)`.

This is the normalized two-point estimate from [OD14, Ex. 10.20(b)-(i)],
used in [OD14, Theorem 10.18]. The positive parameters `α` and `β` represent
`λ ^ (1 / p)` and `(1 - λ) ^ (1 / p)`. This formulation uses those parameters
directly and extends the exercise's positive inputs to nonnegative inputs
at `y = -1` and `y = 1`, using convexity on the closed interval.

**Proof sketch.** Set `t = (β - α) / (β + α)` and `z = y ^ 2`, so that
`0 < t < 1` and `z ∈ [0, 1]`. Apply `biased_power_tangent_le` and
`tangent_at_bias`: the tangent has value `4 / (α + β) ^ 2` at `t ^ 2`
and slope `2 * (β ^ (p - 1) - α ^ (p - 1)) / (β - α)`.
The normalization and real-power subtraction identities identify the
quadratic expression with this tangent evaluated at `z`.
Finally, `√(y ^ 2) = |y|` and symmetry of the inner power sum identify
the resulting bound with the stated right-hand side. -/
theorem normalized_biased_quadratic_le
    (p α β y : ℝ) (hp_one : 1 < p) (hp_two : p < 2)
    (hα_pos : 0 < α) (hαβ : α < β) (hnorm : α ^ p + β ^ p = 1)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    let r : ℝ :=
      (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) /
        (α ^ (2 : ℕ) - β ^ (2 : ℕ))
    (α ^ p * ((1 + y) / α) + β ^ p * ((1 - y) / β)) ^ (2 : ℕ) +
      r * α ^ p * β ^ p *
        (((1 + y) / α) - ((1 - y) / β)) ^ (2 : ℕ) ≤
      ((1 + y) ^ p + (1 - y) ^ p) ^ (2 / p) := by
  let r : ℝ :=
    (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) /
      (α ^ (2 : ℕ) - β ^ (2 : ℕ))
  let t : ℝ := (β - α) / (β + α)
  change
    (α ^ p * ((1 + y) / α) + β ^ p * ((1 - y) / β)) ^ (2 : ℕ) +
      r * α ^ p * β ^ p *
        (((1 + y) / α) - ((1 - y) / β)) ^ (2 : ℕ) ≤
      ((1 + y) ^ p + (1 - y) ^ p) ^ (2 / p)
  have hβ_pos : 0 < β := hα_pos.trans hαβ
  have ht : 0 < t ∧ t < 1 := by
    dsimp only [t]
    constructor
    · exact div_pos (sub_pos.mpr hαβ) (add_pos hβ_pos hα_pos)
    · exact (div_lt_one (add_pos hβ_pos hα_pos)).2 (by linarith)
  have hz : y ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨sq_nonneg y, ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hy.2)
      (by linarith [hy.1] : 0 ≤ 1 + y)]
  obtain ⟨hvalue, hslope⟩ :=
    tangent_at_bias p α β hp_one hp_two hα_pos hαβ hnorm
  have hquad :
      (α ^ p * ((1 + y) / α) + β ^ p * ((1 - y) / β)) ^ (2 : ℕ) +
        r * α ^ p * β ^ p *
          (((1 + y) / α) - ((1 - y) / β)) ^ (2 : ℕ) =
      4 / (α + β) ^ (2 : ℕ) +
        (2 * (β ^ (p - 1) - α ^ (p - 1)) / (β - α)) *
          (y ^ (2 : ℕ) - t ^ (2 : ℕ)) := by
    dsimp only [r, t]
    rw [Real.rpow_sub hα_pos (2 : ℝ) p,
      Real.rpow_sub hβ_pos (2 : ℝ) p]
    simp only [Real.rpow_two]
    rw [Real.rpow_sub_one (ne_of_gt hα_pos) p,
      Real.rpow_sub_one (ne_of_gt hβ_pos) p]
    have hnorm' : β ^ p = 1 - α ^ p := by linarith [hnorm]
    have hden : α ^ (2 : ℕ) - β ^ (2 : ℕ) ≠ 0 :=
      sub_ne_zero.mpr
        (ne_of_lt ((sq_lt_sq₀ hα_pos.le hβ_pos.le).2 hαβ))
    field_simp [ne_of_gt hα_pos, ne_of_gt hβ_pos,
      ne_of_gt (Real.rpow_pos_of_pos hα_pos p),
      ne_of_gt (Real.rpow_pos_of_pos hβ_pos p), hden,
      (sub_pos.mpr hαβ).ne', (add_pos hα_pos hβ_pos).ne',
      (add_pos hβ_pos hα_pos).ne']
    simp only [hnorm']
    ring
  have htan :=
    biased_power_tangent_le p t (y ^ (2 : ℕ))
      hp_one hp_two ht.1 ht.2 hz
  rw [hvalue, hslope, ← hquad] at htan
  rw [Real.sqrt_sq_eq_abs] at htan
  by_cases hy_nonneg : 0 ≤ y
  · simpa only [abs_of_nonneg hy_nonneg] using htan
  · rw [abs_of_neg (lt_of_not_ge hy_nonneg), sub_neg_eq_add] at htan
    simpa only [sub_eq_add_neg, add_comm] using htan

/-- For `1 < p < 2` and `0 < α < β` satisfying `α ^ p + β ^ p = 1`,
the sharp biased two-point inequality holds for nonnegative real inputs
`u` and `v`, with normalized weights `α ^ p` and `β ^ p`.
This is the inequality underlying [OD14, Theorem 10.18], expressed using
the equivalent normalized parameters from [OD14, Ex. 10.20(b)-(c)]:
`α = λ ^ (1 / p)` and `β = (1 - λ) ^ (1 / p)`.
The nonnegative formulation includes zero-valued inputs, extending the
source's positive-input normalization step.

**Proof sketch.** Set `s = α * u + β * v`. If `s = 0`, positivity of `α`
and `β`, together with nonnegativity of the inputs, forces both inputs
to vanish. Otherwise set `k = s / 2` and
`y = (α * u - β * v) / s`. Then `k > 0`, `y ∈ [-1, 1]`,
`u = k * (1 + y) / α`, and `v = k * (1 - y) / β`.
Apply `normalized_biased_quadratic_le` and multiply by `k²`.
The weighted `p` moment equals
`k ^ p * ((1 + y) ^ p + (1 - y) ^ p)`;
real-power multiplication and exponent arithmetic turn its `2 / p`
power into `k²` times the normalized bound. -/
theorem nonnegative_biased_two_point_le (p α β u v : ℝ)
    (hp_one : 1 < p) (hp_two : p < 2)
    (hα_pos : 0 < α) (hαβ : α < β)
    (hnorm : α ^ p + β ^ p = 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    let r := (α ^ p * β ^ (2 - p) - α ^ (2 - p) * β ^ p) /
      (α ^ (2 : ℕ) - β ^ (2 : ℕ))
    (α ^ p * u + β ^ p * v) ^ (2 : ℕ) +
        r * α ^ p * β ^ p * (u - v) ^ (2 : ℕ) ≤
      (α ^ p * u ^ p + β ^ p * v ^ p) ^ (2 / p) := by
  dsimp only
  have hp_pos : 0 < p := by linarith
  have hβ_pos : 0 < β := lt_trans hα_pos hαβ
  by_cases hs : α * u + β * v = 0
  · have hu0 : u = 0 :=
      (mul_eq_zero.mp (show α * u = 0 by
        linarith [mul_nonneg hα_pos.le hu, mul_nonneg hβ_pos.le hv])).resolve_left
          (ne_of_gt hα_pos)
    have hv0 : v = 0 :=
      (mul_eq_zero.mp (by simpa [hu0] using hs)).resolve_left (ne_of_gt hβ_pos)
    simp [hu0, hv0, Real.zero_rpow (ne_of_gt hp_pos),
      Real.zero_rpow (ne_of_gt (div_pos (by norm_num : (0 : ℝ) < 2) hp_pos))]
  · have hs_pos : 0 < α * u + β * v :=
      lt_of_le_of_ne
        (add_nonneg (mul_nonneg hα_pos.le hu) (mul_nonneg hβ_pos.le hv)) (Ne.symm hs)
    -- Normalize the two inputs by their positive common scale.
    let k := (α * u + β * v) / 2
    let y := (α * u - β * v) / (α * u + β * v)
    have hk_pos : 0 < k := div_pos hs_pos (by norm_num)
    have hy : y ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · change -1 ≤ (α * u - β * v) / (α * u + β * v)
        apply (le_div_iff₀ hs_pos).2
        nlinarith [mul_nonneg hα_pos.le hu]
      · change (α * u - β * v) / (α * u + β * v) ≤ 1
        apply (div_le_iff₀ hs_pos).2
        nlinarith [mul_nonneg hβ_pos.le hv]
    have hy_mul : y * (α * u + β * v) = α * u - β * v := by
      exact div_mul_cancel₀ _ (ne_of_gt hs_pos)
    have hu_scale : u = k * ((1 + y) / α) := by
      apply mul_right_cancel₀ (ne_of_gt hα_pos)
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hα_pos)]
      dsimp only [k]
      nlinarith [hy_mul]
    have hv_scale : v = k * ((1 - y) / β) := by
      apply mul_right_cancel₀ (ne_of_gt hβ_pos)
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hβ_pos)]
      dsimp only [k]
      nlinarith [hy_mul]
    have hyp : 0 ≤ 1 + y := by linarith [hy.1]
    have hym : 0 ≤ 1 - y := by linarith [hy.2]
    -- Both sides scale quadratically, so the normalized inequality applies.
    have hmoment : α ^ p * u ^ p + β ^ p * v ^ p =
        k ^ p * ((1 + y) ^ p + (1 - y) ^ p) := by
      rw [hu_scale, hv_scale,
        Real.mul_rpow hk_pos.le (div_nonneg hyp hα_pos.le),
        Real.mul_rpow hk_pos.le (div_nonneg hym hβ_pos.le),
        Real.div_rpow hyp hα_pos.le p, Real.div_rpow hym hβ_pos.le p]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hα_pos p),
        ne_of_gt (Real.rpow_pos_of_pos hβ_pos p)] <;> ring
    convert mul_le_mul_of_nonneg_left
      (normalized_biased_quadratic_le p α β y hp_one hp_two hα_pos hαβ hnorm hy)
      (sq_nonneg k) using 1
    · rw [hu_scale, hv_scale]
      ring
    · rw [hmoment,
        Real.mul_rpow (Real.rpow_nonneg hk_pos.le p)
          (add_nonneg (Real.rpow_nonneg hyp p) (Real.rpow_nonneg hym p)),
        ← Real.rpow_mul hk_pos.le p (2 / p)]
      have hcancel : p * (2 / p) = 2 := by
        field_simp [ne_of_gt hp_pos] <;> ring
      rw [hcancel, Real.rpow_two]

end SharpDiscrete

end BooleanAnalysis.Hypercontractivity
