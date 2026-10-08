/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteNoiseContraction
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Sharp.FiniteNoiseDuality
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.FiniteLaw

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharp hypercontractivity for discrete random variables

This module transfers the full finite weighted noise-operator bound to
affine perturbations of discrete random variables on arbitrary probability
spaces.

## Main definitions

No new definitions are introduced. The random-variable layer supplies
`IsHypercontractive` and `HasAtomLowerBound`, and the parameter layer supplies
`sharpDiscreteRadius`.

## Main results

* `finite_law_sharp_forward`: a centered measurable real random variable
  with atom masses bounded below is hypercontractive from two to `q`
  at the sharp discrete radius.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §8.1, Definition 9.13, Proposition 9.19 (proof), Theorem 10.18,
  equation (10.5), and Exercises 10.18(a), 10.19–10.20.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.Hypercontractivity.SharpDiscrete

/-- For `q > 2` and `0 < lam < 1 / 2`, a centered measurable real random
variable on a probability space, with almost-everywhere finite support and
every supported atom of mass at least `lam`, is hypercontractive from
exponent two to `q` at the sharp discrete radius.

This is the forward direction of [OD14, Theorem 10.18, equation (10.5)],
using [OD14, Exercises 10.19–10.20]. The atom lower-bound formulation uses
[OD14, Exercise 10.18(a)]. The sample space is arbitrary; finite support
provides the required integrability and finite norms.

**Proof sketch.** Extract the finite supporting set and use its subtype as
the finite index type. The real fiber weights sum to one and are at least
`lam`, hence positive. Apply sharp finite conjugate contraction, then full
finite noise-operator duality to obtain the forward two-to-`q` bound for
every real function on this support. Apply that bound to the affine function
`x ↦ a + b * x`. The finite-law mean formula and centering make its weighted
mean equal to `a`, so its noise transform is `x ↦ a + rho * b * x`.
The finite-law norm formulas identify the weighted moment inequality with
the comparison of squared real norms. Nonnegativity removes the squares.
Finite-support membership in the required `Lᵖ` spaces transfers this
comparison to the extended norms defining hypercontractivity. The exponent
assumption and established radius bounds supply its remaining conditions. -/
theorem finite_law_sharp_forward {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (q lam : ℝ)
    (hq : 2 < q) (hlam_pos : 0 < lam) (hlam_lt_half : lam < 1 / 2)
    (hX : Measurable X) (hatoms : HasAtomLowerBound X μ lam)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    IsHypercontractive X μ 2 (ENNReal.ofReal q) (sharpDiscreteRadius q lam) := by
  classical
  have hqpos : 0 < q := by linarith
  have hmem (r : ℝ≥0∞) : MemLp X r μ := hatoms.memLp hX r
  obtain ⟨s, hs, hbound⟩ := hatoms
  let rho : ℝ := sharpDiscreteRadius q lam
  let w : s → ℝ := fun x => (μ {ω | X ω = (x : ℝ)}).toReal
  obtain ⟨hmass, hlower⟩ :=
    FiniteLaw.finite_probability_atom_weights μ X s hX hs lam hlam_pos.le hbound
  have hw_sum : ∑ x : s, w x = 1 := by
    change (∑ x : s, (μ {ω | X ω = (x : ℝ)}).toReal) = 1
    rw [Finset.sum_coe_sort s (fun x : ℝ => (μ {ω | X ω = x}).toReal)]
    exact hmass
  have hw_lower (x : s) : lam ≤ w x := hlower x x.property
  have hcenter : ∑ x : s, w x * (x : ℝ) = 0 := by
    change (∑ x : s, (μ {ω | X ω = (x : ℝ)}).toReal * (x : ℝ)) = 0
    rw [Finset.sum_coe_sort s (fun x : ℝ => (μ {ω | X ω = x}).toReal * x)]
    exact (FiniteLaw.finite_law_integral μ X s hX hs (fun x => x)).symm.trans hmean
  -- Full finite duality supplies the forward bound on the support.
  have hforward := finite_noise_duality w
    (fun x => (lt_of_lt_of_le hlam_pos (hw_lower x)).le) hw_sum q hq rho
    (finite_noise_sharp_contraction w hw_sum q lam hq hlam_pos hlam_lt_half hw_lower)
  have hr := radius_pos_lt_one q lam hq hlam_pos hlam_lt_half
  refine ⟨by norm_num, ?_, hr.1.le, hr.2, hmem _, ?_⟩
  · simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hq.le
  · intro a b
    have houtmem : MemLp (fun ω => a + rho * b * X ω) (ENNReal.ofReal q) μ :=
      (memLp_const a).add ((hmem (ENNReal.ofReal q)).const_mul (rho * b))
    have hinmem : MemLp (fun ω => a + b * X ω) 2 μ :=
      (memLp_const a).add ((hmem 2).const_mul b)
    have haffine : (∑ x : s, w x * (a + b * (x : ℝ))) = a := by
      calc
        _ = (∑ x : s, w x) * a + (∑ x : s, w x * (x : ℝ)) * b := by
          rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = a := by rw [hw_sum, hcenter]; ring
    have hscalar := hforward (fun x : s => a + b * (x : ℝ))
    rw [haffine] at hscalar
    simp_rw [show ∀ x : s,
      rho * (a + b * (x : ℝ)) + (1 - rho) * a =
        a + rho * b * (x : ℝ) by intro x; ring] at hscalar
    dsimp only [w] at hscalar
    rw [Finset.sum_coe_sort s
        (fun x : ℝ => (μ {ω | X ω = x}).toReal * |a + rho * b * x| ^ q),
      Finset.sum_coe_sort s
        (fun x : ℝ => (μ {ω | X ω = x}).toReal * (a + b * x) ^ (2 : ℕ))] at hscalar
    -- The finite-law formulas identify the squared real norms.
    have hsquare :
        rvLpNorm (fun ω => a + rho * b * X ω) μ q ^ (2 : ℕ) ≤
          rvLpNorm (fun ω => a + b * X ω) μ 2 ^ (2 : ℕ) := by
      rw [FiniteLaw.finite_law_affine_norm_sq μ X s hX hs q hqpos a (rho * b),
        FiniteLaw.finite_law_affine_norm_sq μ X s hX hs 2 (by norm_num) a b]
      norm_num only [Real.rpow_two, sq_abs, Real.rpow_one]
      exact hscalar
    apply (ENNReal.toReal_le_toReal houtmem.2.ne hinmem.2.ne).1
    apply (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (by decide : (2 : ℕ) ≠ 0)).1
    simpa only [rvLpNorm, ENNReal.ofReal_ofNat] using hsquare

end BooleanAnalysis.Hypercontractivity.SharpDiscrete
