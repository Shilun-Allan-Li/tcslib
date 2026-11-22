/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Localization for Gaussian energy estimates

## Main definitions

Smooth bump functions and the existing Gaussian coordinate space are reused.

## Main results

* `exists_gaussian_smooth_cutoff_sequence`: compact smooth cutoffs converge to
  one while their coordinate derivatives vanish and remain uniformly bounded.
* `integrable_of_nonneg_tendsto_integral_bounded`: a Fatou criterion for
  integrability from uniformly bounded nonnegative approximation integrals.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Proposition 11.28, localization argument.
-/

open MeasureTheory Filter Metric
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

/-- Finite-dimensional Gaussian space has smooth compact cutoffs equal to one
on the radius-R ball, valued in [0,1], with derivative bounded by C/R.
[OD14, §11.1, localization for Gaussian integration by parts]
**Proof sketch.** Dilate one fixed smooth bump. Compact support bounds its
derivative, and dilation divides that bound by the radius. -/
lemma exists_gaussian_smooth_cutoffs (n : ℕ) :
    ∃ (χ : ℝ → (Fin n → ℝ) → ℝ) (C : ℝ), 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ContDiff ℝ (↑(⊤ : ℕ∞)) (χ R) ∧ HasCompactSupport (χ R) ∧
      (∀ x, χ R x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, ‖x‖ ≤ R → χ R x = 1) ∧
      (∀ x, ‖fderiv ℝ (χ R) x‖ ≤ C / R) := by
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hbc : ContDiff ℝ (↑(⊤ : ℕ∞)) (b : (Fin n → ℝ) → ℝ) := b.contDiff
  obtain ⟨C, hC⟩ := (b.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hbc.continuous_fderiv (by norm_num))
  refine ⟨fun R x => b (R⁻¹ • x), C, (norm_nonneg _).trans (hC 0), ?_⟩
  intro R hR
  refine ⟨hbc.comp (contDiff_const.smul contDiff_id),
    b.hasCompactSupport.comp_smul (inv_ne_zero hR.ne'), ?_, ?_, ?_⟩
  · intro x
    exact ⟨b.nonneg, b.le_one⟩
  · intro x hx
    apply b.one_of_mem_closedBall
    change dist (R⁻¹ • x) 0 ≤ 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    simpa only [inv_mul_cancel₀ hR.ne'] using
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
  · intro x
    rw [fderiv_comp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (hC (R⁻¹ • x)) (inv_nonneg.mpr hR.le)

/-- There are smooth compact cutoffs converging pointwise to one whose
coordinate derivatives converge pointwise to zero and are uniformly bounded.
[OD14, §11.1, localization for Gaussian integration by parts]
**Proof sketch.** Use the radius-k+1 dilations. Every point eventually lies in
the region where the cutoff is one; derivative bounds decay as 1/(k+1). -/
lemma exists_gaussian_smooth_cutoff_sequence (n : ℕ) :
    ∃ (χ : ℕ → (Fin n → ℝ) → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ k, ContDiff ℝ (↑(⊤ : ℕ∞)) (χ k) ∧ HasCompactSupport (χ k) ∧
        (∀ x, χ k x ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ x, ‖fderiv ℝ (χ k) x‖ ≤ C / ((k : ℝ) + 1)) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ x i, Tendsto (fun k => fderiv ℝ (χ k) x (Pi.single i 1)) atTop (𝓝 0)) ∧
      (∀ k x i, ‖fderiv ℝ (χ k) x (Pi.single i 1)‖ ≤ C) := by
  obtain ⟨ψ, C, hC, hψ⟩ := exists_gaussian_smooth_cutoffs n
  let χ := fun (k : ℕ) => ψ ((k : ℝ) + 1)
  have hp (k : ℕ) : 0 < (k : ℝ) + 1 := by positivity
  have hd (k : ℕ) (x : Fin n → ℝ) (i : Fin n) :
      ‖fderiv ℝ (χ k) x (Pi.single i 1)‖ ≤ C / ((k : ℝ) + 1) := by
    apply le_trans ?_ ((hψ _ (hp k)).2.2.2.2 x)
    simpa only [Pi.norm_single, norm_one, mul_one] using
      (fderiv ℝ (χ k) x).le_opNorm (Pi.single i 1)
  refine ⟨χ, C, hC, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hψ _ (hp k)).1, (hψ _ (hp k)).2.1,
      (hψ _ (hp k)).2.2.1, (hψ _ (hp k)).2.2.2.2⟩
  · intro x
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    filter_upwards [eventually_ge_atTop N] with k hk
    symm
    apply (hψ _ (hp k)).2.2.2.1
    exact hN.trans ((by exact_mod_cast hk : (N : ℝ) ≤ k).trans (by linarith))
  · intro x i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hmajor : Tendsto (fun k : ℕ => C / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun k => norm_nonneg _) (fun k => hd k x i)
  · intro k x i
    exact (hd k x i).trans (div_le_self hC (by have := Nat.cast_nonneg (α := ℝ) k; linarith))

/-- An almost-everywhere limit of nonnegative integrable functions is integrable
if their integrals admit a common finite upper bound and the limit is measurable.
**Proof sketch.** Fatou's inequality bounds the limit's L¹ seminorm by the
liminf of the approximating seminorms, each bounded by the common constant. -/
lemma integrable_of_nonneg_tendsto_integral_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hF : ∀ k, Integrable (F k) μ) (hfn : ∀ k x, 0 ≤ F k x)
    (hf : AEStronglyMeasurable f μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (f x)))
    (hbound : ∀ k, ∫ x, F k x ∂μ ≤ C) : Integrable f μ := (by
    apply memLp_one_iff_integrable.mp
    refine ⟨hf, lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun k => (hF k).aestronglyMeasurable) f hlim) ?_⟩
    apply lt_of_le_of_lt (liminf_le_of_frequently_le' (x := ENNReal.ofReal C) ?_) ENNReal.ofReal_lt_top
    apply Eventually.frequently
    apply Eventually.of_forall
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hF k)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_of_nonneg (hfn k _)] using hbound k
)

end BooleanAnalysis.GaussianSpace
