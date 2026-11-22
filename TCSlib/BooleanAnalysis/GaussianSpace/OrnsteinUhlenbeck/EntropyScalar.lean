/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Power secants and entropy rescaling

## Main definitions

Real powers, logarithms, and integrals are reused; no new definitions are introduced.

## Main results

* `integrable_mul_log_of_power_secants`: power-secant bounds imply entropy
  integrability and an integral bound.
* `integral_mul_log_rescale`: normalized entropy rescales by the original mass.

Scalar secant estimates and a Fatou criterion support the Gaussian
log-Sobolev argument without assuming entropy integrability in advance.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian Log-Sobolev inequality.
-/

open Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace BooleanAnalysis.GaussianSpace

/-- Power secants approaching exponent one from below have the uniform lower
bound a-1. [OD14, §11.1, entropy differentiation]
**Proof sketch.** Weighted arithmetic-geometric mean bounds a^(1-ε) by
(1-ε)a+ε; rearrange and divide by ε. -/
lemma entropy_power_secant_lower {a ε : ℝ} (ha : 0 ≤ a)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    a - 1 ≤ (a - a ^ (1 - ε)) / ε := by
  have hp := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr hε1) hε.le ha (by norm_num : (0 : ℝ) ≤ 1)
    (show (1 - ε) + ε = 1 by ring)
  simp only [Real.one_rpow, mul_one] at hp
  apply (le_div_iff₀ hε).mpr
  nlinarith

/-- Power secants at exponent one converge to a log a, including a=0.
[OD14, §11.1, entropy differentiation]
**Proof sketch.** At positive a, differentiate its real power in the exponent.
At zero, every nearby exponent is positive and the secants vanish. -/
lemma tendsto_entropy_power_secant {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε : ℝ => (a - a ^ (1 - ε)) / ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (a * Real.log a)) := by
  by_cases hz : a = 0
  · subst a
    simp only [Real.log_zero, zero_mul]
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with ε hε
    simp only [Real.zero_rpow (by linarith : 1 - ε ≠ 0), sub_self, zero_div]
  · have hp : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hd : HasDerivAt (fun ε : ℝ => a ^ (1 - ε)) (-(a * Real.log a)) 0 := by
      convert (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id' 0)).const_rpow hp) using 1 <;>
        simp <;> ring
    have ht := hd.tendsto_slope_zero_right.neg
    convert ht using 1
    · funext ε
      simp only [zero_add, sub_zero, Real.rpow_one, smul_eq_mul]
      ring
    · ring

/-- Fatou's inequality preserves a convergent upper bound on integrals of
nonnegative functions, and proves integrability of the limit.
**Proof sketch.** Lower semicontinuity bounds the limiting L¹ seminorm by the
liminf of the approximating seminorms. Nonnegativity identifies each seminorm
with its integral; the convergent upper bounds give finiteness and the inequality. -/
lemma integrable_integral_le_of_nonneg_tendsto_integral_upper
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {b : ℕ → ℝ} {C : ℝ}
    (hF : ∀ k, Integrable (F k) μ) (hFn : ∀ k x, 0 ≤ F k x)
    (hf : AEStronglyMeasurable f μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (f x)))
    (hupper : ∀ k, ∫ x, F k x ∂μ ≤ b k)
    (hb : Tendsto b atTop (𝓝 C)) : Integrable f μ ∧ ∫ x, f x ∂μ ≤ C := by
  have hC : 0 ≤ C := ge_of_tendsto hb
    (Eventually.of_forall fun k => (integral_nonneg (hFn k)).trans (hupper k))
  have hnorm (k : ℕ) : eLpNorm (F k) 1 μ ≤ ENNReal.ofReal (b k) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hF k)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_of_nonneg (hFn k _)] using hupper k
  have hbound : eLpNorm f 1 μ ≤ ENNReal.ofReal C := by
    apply (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun k => (hF k).aestronglyMeasurable) f hlim).trans
    exact (liminf_le_liminf (Eventually.of_forall hnorm)).trans_eq
      (ENNReal.continuous_ofReal.tendsto C |>.comp hb).liminf_eq
  have hint : Integrable f μ := memLp_one_iff_integrable.mp
    ⟨hf, hbound.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  have hfn : ∀ᵐ x ∂μ, 0 ≤ f x := hlim.mono fun x hx =>
    ge_of_tendsto hx (Eventually.of_forall fun k => hFn k x)
  have heq : ENNReal.ofReal (∫ x, f x ∂μ) = eLpNorm f 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hint]
    congr 1
    apply integral_congr_ae
    filter_upwards [hfn] with x hx
    exact (Real.norm_of_nonneg hx).symm
  rw [heq]
  exact hbound

/-- Upper bounds on integrals of power secants give entropy integrability and
an upper bound on its integral. [OD14, §11.1, entropy differentiation]
**Proof sketch.** Add one to each secant to make it nonnegative. The scalar
secants converge to a log a; Fatou bounds the integral and proves integrability.
Subtract the integrable constant one. -/
lemma integrable_mul_log_of_power_secants
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {a : α → ℝ} (ha : ∀ x, 0 ≤ a x) (ham : AEStronglyMeasurable a μ)
    {ε : ℕ → ℝ} (hε0 : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hQ : ∀ k, Integrable (fun x => (a x - a x ^ (1 - ε k)) / ε k) μ)
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hupper : ∀ k, ∫ x, (a x - a x ^ (1 - ε k)) / ε k ∂μ ≤ b k) :
    Integrable (fun x => a x * Real.log (a x)) μ ∧
      (∫ x, a x * Real.log (a x) ∂μ) ≤ B := by
  have hshift := integrable_integral_le_of_nonneg_tendsto_integral_upper
    (F := fun k x => (a x - a x ^ (1 - ε k)) / ε k + 1)
    (f := fun x => a x * Real.log (a x) + 1)
    (b := fun k => b k + 1) (C := B + 1)
    (fun k => (hQ k).add (integrable_const 1))
    (fun k x => by
      have := entropy_power_secant_lower (ha x) (hε0 k) (hε1 k)
      linarith [ha x])
    ((Real.continuous_mul_log.comp_aestronglyMeasurable ham).add aestronglyMeasurable_const)
    (Eventually.of_forall fun x => ((tendsto_entropy_power_secant (ha x)).comp hεlim).add_const 1)
    (fun k => by
      rw [integral_add (hQ k) (integrable_const 1)]
      simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one] using
        add_le_add_right (hupper k) 1)
    (hb.add_const 1)
  have hint : Integrable (fun x => a x * Real.log (a x)) μ := by
    have hh := hshift.1.sub (integrable_const 1)
    change Integrable (fun x => (a x * Real.log (a x) + 1) - 1) μ at hh
    simpa only [add_sub_cancel_right] using hh
  refine ⟨hint, ?_⟩
  have hbound := hshift.2
  rw [integral_add hint (integrable_const 1)] at hbound
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one] at hbound
  linarith

end BooleanAnalysis.GaussianSpace

open MeasureTheory Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace

/-- Multiplication by the logarithm splits into a normalized entropy term and
a mass logarithm under a positive scalar rescaling.
**Proof sketch.** The zero case is immediate; otherwise expand the logarithm
of the quotient and cancel its nonzero denominator. -/
lemma mul_log_eq_rescale (a : ℝ) {A : ℝ} (hA : 0 < A) :
    a * Real.log a = A * ((a / A) * Real.log (a / A)) + Real.log A * a := by
  by_cases ha : a = 0
  · simp only [ha, zero_div, zero_mul, mul_zero, add_zero]
  · rw [Real.log_div ha (ne_of_gt hA)]
    field_simp [ne_of_gt hA]
    ring

/-- Integrability of normalized entropy and of the original function gives
integrability of its entropy integrand; its entropy rescales by the total mass.
**Proof sketch.** Integrate the scalar logarithmic rescaling identity. Both
terms on its right are integrable by the assumptions and scalar multiplication. -/
lemma integral_mul_log_rescale
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {a : α → ℝ}
    (ha : Integrable a μ) (hA : 0 < ∫ x, a x ∂μ)
    (hnorm : Integrable (fun x => (a x / (∫ y, a y ∂μ)) *
      Real.log (a x / (∫ y, a y ∂μ))) μ) :
    Integrable (fun x => a x * Real.log (a x)) μ ∧
      (∫ x, a x * Real.log (a x) ∂μ) - (∫ x, a x ∂μ) * Real.log (∫ x, a x ∂μ) =
        (∫ x, a x ∂μ) * ∫ x, (a x / (∫ y, a y ∂μ)) *
          Real.log (a x / (∫ y, a y ∂μ)) ∂μ := (by
    let A := ∫ x, a x ∂μ
    have hscaled : Integrable (fun x => A * ((a x / A) * Real.log (a x / A))) μ :=
      hnorm.const_mul A
    have hmass : Integrable (fun x => Real.log A * a x) μ := ha.const_mul (Real.log A)
    have heq : (fun x => a x * Real.log (a x)) =
        (fun x => A * ((a x / A) * Real.log (a x / A)) + Real.log A * a x) := by
      funext x
      exact mul_log_eq_rescale (a x) hA
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact hscaled.add hmass
    · change (∫ x, a x * Real.log (a x) ∂μ) - A * Real.log A =
        A * ∫ x, (a x / A) * Real.log (a x / A) ∂μ
      rw [heq, integral_add hscaled hmass, integral_const_mul, integral_const_mul]
      change A * (∫ x, (a x / A) * Real.log (a x / A) ∂μ) + Real.log A * A -
        A * Real.log A = A * ∫ x, (a x / A) * Real.log (a x / A) ∂μ
      ring
)

end BooleanAnalysis.GaussianSpace
