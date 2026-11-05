/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Linear

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Integration against Gaussian noise kernels

## Main definitions

The Mehler operator and the finite product Gaussian law are reused.

## Main results

* `integral_gaussian_affine_pair`: combine two independent Gaussian increments.
* `integral_correlatedGaussianMeasure_of_integrable`: identify a jointly integrable
  correlated product with its conditional-noise integral.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian noise and the Mehler semigroup.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Two independent Gaussian increments can be combined into one increment with
the same variance, even inside a translated average.
[OD14, §11.1, Mehler semigroup]

**Proof sketch.** If the variance vanishes, both increments vanish. Otherwise,
divide both coefficients by the resulting standard deviation. Their squares
sum to one, so their linear combination is standard Gaussian. Push forward the
translated integrand through this measure-preserving combination. -/
lemma integral_gaussian_affine_pair (a : Fin n → ℝ) (b c v : ℝ)
    (hc : 0 ≤ c) (hv : 0 ≤ v) (hsq : b ^ 2 + c ^ 2 = v ^ 2)
    {f : (Fin n → ℝ) → ℝ} (hf : StronglyMeasurable f) :
    (∫ z, f (fun i => a i + b * z.1 i + c * z.2 i) ∂(γ).prod γ) =
      ∫ y, f (fun i => a i + v * y i) ∂γ := by
  by_cases hv0 : v = 0
  · have hb : b = 0 := by nlinarith [sq_nonneg c]
    have hc0 : c = 0 := by nlinarith [sq_nonneg b]
    simp [hv0, hb, hc0]
  · have hunit : (b / v) ^ 2 + (c / v) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, hsq, div_self (pow_ne_zero 2 hv0)]
    have hp := measurePreserving_gaussianCombination (n := n)
      (b / v) (c / v) (div_nonneg hc hv) hunit
    let g := fun y : Fin n → ℝ => f (fun i => a i + v * y i)
    have hg : StronglyMeasurable g := hf.comp_measurable (by fun_prop)
    calc
      _ = ∫ z, g (fun i => b / v * z.1 i + c / v * z.2 i) ∂(γ).prod γ := by
        apply integral_congr_ae
        filter_upwards [] with z
        change f _ = f _
        congr 1
        funext i
        dsimp
        field_simp
        ring
      _ = ∫ y, g y ∂γ := by
        conv_rhs => rw [← hp.map_eq]
        exact (integral_map hp.measurable.aemeasurable hg.aestronglyMeasurable).symm

/-- Expanding two consecutive Gaussian averages gives a jointly integrable
three-vector integrand for every Gaussian integrable input.
[OD14, §11.1, Mehler semigroup]

**Proof sketch.** First combine the first two Gaussian vectors using the first
correlation, then combine the result with the third using the second correlation.
Both maps preserve the appropriate Gaussian product laws. -/
lemma integrable_gaussianNoise_compose_integrand {ρ σ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hσ : σ ∈ Set.Icc (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    Integrable
      (fun z : (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        f (fun i => σ * (ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2.1 i) +
          Real.sqrt (1 - σ ^ 2) * z.2.2 i))
      ((γ).prod ((γ).prod γ)) := by
  exact ((measurePreserving_gaussianEndpoint hσ).comp
    (((measurePreserving_gaussianEndpoint hρ).prod (MeasurePreserving.id γ)).comp
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (measurePreserving_prodAssoc γ γ γ)))).integrable_comp_of_integrable hf

/-- Composing Gaussian noise multiplies correlations for a strongly measurable,
Gaussian integrable input. [OD14, §11.1, Mehler semigroup]

**Proof sketch.** Joint integrability gives Fubini on almost every section with
the first vector fixed. Expand the two averages, then combine their independent
increments using the variance identity. -/
lemma gaussianNoise_compose_stronglyMeasurable {ρ σ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hσ : σ ∈ Set.Icc (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) (hm : StronglyMeasurable f) :
    gaussianNoise ρ (gaussianNoise σ f) =ᵐ[γ] gaussianNoise (ρ * σ) f := by
  filter_upwards [(integrable_gaussianNoise_compose_integrand hρ hσ hf).prod_right_ae]
    with x hx
  change (∫ y, ∫ z,
    f (fun i => σ * (ρ * x i + Real.sqrt (1 - ρ ^ 2) * y i) +
      Real.sqrt (1 - σ ^ 2) * z i) ∂γ ∂γ) = _
  rw [← integral_prod _ hx]
  calc
    _ = ∫ z, f (fun i => (ρ * σ) * x i +
        (σ * Real.sqrt (1 - ρ ^ 2)) * z.1 i +
        Real.sqrt (1 - σ ^ 2) * z.2 i) ∂(γ).prod γ := by
      apply integral_congr_ae
      filter_upwards [] with z
      congr 1
      funext i
      ring
    _ = _ := integral_gaussian_affine_pair (fun i => (ρ * σ) * x i)
      (σ * Real.sqrt (1 - ρ ^ 2)) (Real.sqrt (1 - σ ^ 2))
      (Real.sqrt (1 - (ρ * σ) ^ 2)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (gaussianNoise_increment_variance hρ hσ) hm

/-- Products of two Gaussian square-integrable inputs are integrable along a
correlated Gaussian coupling. [OD14, §11.1, Gaussian noise inner product]

**Proof sketch.** Both endpoint projections preserve the standard Gaussian law.
Pull back the two square-integrability bounds and apply Cauchy–Schwarz. -/
lemma integrable_gaussianNoise_pair_mul {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      f z.1 * g (fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i))
      ((γ).prod γ) := by
  exact (hf.comp_measurePreserving measurePreserving_fst).integrable_mul
    (hg.comp_measurePreserving (measurePreserving_gaussianEndpoint hρ))

/-- Averaging one probability coordinate of a product contracts every Lp norm
with exponent at least one, including the essential supremum.
[OD14, Prop. 11.15, conditional Jensen step]

**Proof sketch.** Each section's mean is bounded by its L1 norm and hence its
Lp norm. Integrate the pth powers using Fubini. At infinity, transfer the joint
essential bound to almost every section instead. -/
lemma eLpNorm_integral_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν]
    (p : ℝ≥0∞) (hp : 1 ≤ p) {F : α × β → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod ν)) :
    eLpNorm (fun x => ∫ y, F (x, y) ∂ν) p μ ≤ eLpNorm F p (μ.prod ν) := by
  have hslice : ∀ᵐ x ∂μ, ‖∫ y, F (x, y) ∂ν‖ₑ ≤ eLpNorm (fun y => F (x, y)) p ν := by
    filter_upwards [hF.prodMk_left] with x hx
    calc
      _ ≤ ∫⁻ y, ‖F (x, y)‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ _ := by
        rw [← eLpNorm_one_eq_lintegral_enorm]
        exact eLpNorm_le_eLpNorm_of_exponent_le hp hx
  by_cases hptop : p = ⊤
  · subst p
    simp only [eLpNorm_exponent_top] at hslice ⊢
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [hslice, Measure.ae_ae_of_ae_prod
      (ae_le_eLpNormEssSup (f := F) (μ := μ.prod ν))] with x hx hbound
    exact hx.trans (eLpNormEssSup_le_of_ae_enorm_bound hbound)
  · have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    have hppos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop,
      eLpNorm_eq_lintegral_rpow_enorm hp0 hptop]
    apply ENNReal.rpow_le_rpow ?_ (by positivity)
    rw [lintegral_prod _ (hF.enorm.pow_const _)]
    apply lintegral_mono_ae
    filter_upwards [hslice] with x hx
    calc
      _ ≤ (eLpNorm (fun y => F (x, y)) p ν) ^ p.toReal :=
        ENNReal.rpow_le_rpow hx hppos.le
      _ = _ := by
        rw [eLpNorm_eq_eLpNorm' hp0 hptop,
          lintegral_rpow_enorm_eq_rpow_eLpNorm' hppos]

/-- A jointly integrable correlated product equals its conditional-noise
integral, without requiring either factor to be square-integrable.
[OD14, §11.1, Gaussian Hypercontractivity display]

**Proof sketch.** Pull the integrand back through the defining coupling and use
Fubini. A factor depending only on the first endpoint leaves the inner integral. -/
lemma integral_correlatedGaussianMeasure_of_integrable (ρ : ℝ)
    {f g : (Fin n → ℝ) → ℝ}
    (hi : Integrable (fun z => f z.1 * g z.2) (correlatedGaussianMeasure ρ)) :
    (∫ z, f z.1 * g z.2 ∂correlatedGaussianMeasure ρ) =
      ∫ x, f x * gaussianNoise ρ g x ∂γ := by
  let C := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    (z.1, fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i)
  have hC : MeasurePreserving C ((γ).prod γ) (correlatedGaussianMeasure ρ) :=
    ⟨by fun_prop, rfl⟩
  calc
    _ = ∫ z, f z.1 * g (fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i)
        ∂(γ).prod γ := integral_map hC.measurable.aemeasurable hi.aestronglyMeasurable
    _ = _ := by
      rw [integral_prod (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        f z.1 * g (fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i))
        (hC.integrable_comp_of_integrable hi)]
      simp only [gaussianNoise, integral_const_mul]

end BooleanAnalysis.GaussianSpace
