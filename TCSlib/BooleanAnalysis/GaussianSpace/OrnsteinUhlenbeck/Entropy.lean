/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.EntropyNormalized
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.TestFunctions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian log-Sobolev from the strong generator limit

## Main definitions

Gaussian noise, strong generator quotients, and entropy integrals are reused.

## Main results

* `tendsto_gaussianNoise_energy_deficit_of_strong_limit`: the strong generator
  limit determines the derivative of the squared Gaussian noise norm.
* `gaussian_entropy_of_strong_limit`: Gaussian log-Sobolev and entropy
  integrability hold under the explicit strong generator assumptions.

Self-adjointness converts the squared noisy norm to a doubled-time pairing.
The normalized entropy bound and mass rescaling finish the inequality without
requiring pointwise smoothness or an entropy integrability assumption.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian Log-Sobolev inequality.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- The square norm of the Gaussian noise orbit equals its doubled-time
pairing with the initial function. [OD14, §11.1, Mehler semigroup]
**Proof sketch.** Use self-adjointness to move one noise operator to the other
factor, then compose the two equal-time noise operators. -/
lemma integral_sq_gaussianNoise_exp_neg {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 γ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, (gaussianNoise (Real.exp (-t)) f x)^2 ∂γ) =
      ∫ x, f x * gaussianNoise (Real.exp (-(2*t))) f x ∂γ := by
  have hρ : Real.exp (-t) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_trans (by norm_num) (Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)⟩
  have hcomp := gaussianNoise_compose hρ hρ (hf.integrable (by norm_num))
  have hexp : Real.exp (-t) * Real.exp (-t) = Real.exp (-(2*t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hcomp
  calc
    _ = ∫ x, gaussianNoise (Real.exp (-t)) f x *
        gaussianNoise (Real.exp (-t)) f x ∂γ := by simp only [pow_two]
    _ = ∫ x, f x * gaussianNoise (Real.exp (-t))
        (gaussianNoise (Real.exp (-t)) f) x ∂γ :=
      (gaussianNoise_selfAdjoint hρ hf (gaussianNoise_memLp hρ 2 (by norm_num) hf)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hcomp] with x hx
      rw [hx]

/-- A strong Gaussian L² generator limit differentiates the loss of squared
Gaussian norm at time zero. [OD14, §11.1, Proposition 11.28]
**Proof sketch.** Self-adjointness identifies the noisy squared norm with a
doubled-time pairing. The difference quotient is twice the pairing of the
initial function with its doubled-time generator quotient; strong L²
convergence gives its limit. -/
lemma tendsto_gaussianNoise_energy_deficit_of_strong_limit
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ)
    (hlim : Tendsto (fun t : ℝ => eLpNorm
      (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x) 2 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun t : ℝ =>
      ((∫ x, (f x)^2 ∂γ) - (∫ x, (gaussianNoise (Real.exp (-t)) f x)^2 ∂γ)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * ∫ x, f x * g x ∂γ)) := by
  let q (t : ℝ) := fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t
  have hρ {t : ℝ} (ht : 0 < t) : Real.exp (-t) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_trans (by norm_num) (Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
  have hq {t : ℝ} (ht : 0 < t) : MemLp (q t) 2 γ := by
    convert (hf.sub (gaussianNoise_memLp (hρ ht) 2 (by norm_num) hf)).const_smul t⁻¹ using 1
    ext x
    change (f x - gaussianNoise (Real.exp (-t)) f x) / t =
      t⁻¹ * (f x - gaussianNoise (Real.exp (-t)) f x)
    ring
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hp : Tendsto (fun t => ∫ x, f x * q t x ∂γ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x * g x ∂γ)) :=
    tendsto_integral_mul_of_eLpNorm_sub_tendsto hf hg
      (htpos.mono fun t ht => hq ht) hlim
  have htime : Tendsto (fun t : ℝ => 2*t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun t : ℝ => 2*t) := continuous_const.mul continuous_id
      simpa only [mul_zero] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [htpos] with t ht
      change 0 < 2*t
      exact mul_pos (by norm_num) ht
  have hconv := (hp.comp htime).const_mul 2
  apply hconv.congr'
  filter_upwards [htpos] with t ht
  have ht2 : 0 < 2*t := mul_pos (by norm_num) ht
  have hnum : (∫ x, (f x)^2 ∂γ) -
      (∫ x, f x * gaussianNoise (Real.exp (-(2*t))) f x ∂γ) =
      ∫ x, f x * (f x - gaussianNoise (Real.exp (-(2*t))) f x) ∂γ := by
    simp only [pow_two]
    rw [← integral_sub
      (show Integrable (fun x => f x*f x) γ from hf.integrable_mul hf)
      (show Integrable (fun x => f x*gaussianNoise (Real.exp (-(2*t))) f x) γ from
        hf.integrable_mul (gaussianNoise_memLp (hρ ht2) 2 (by norm_num) hf))]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  change 2 * (∫ x, f x * ((f x-gaussianNoise (Real.exp (-(2*t))) f x)/(2*t)) ∂γ) = _
  rw [integral_sq_gaussianNoise_exp_neg hf ht.le, hnum]
  simp_rw [← mul_div_assoc]
  rw [integral_div]
  field_simp [ne_of_gt ht]

end BooleanAnalysis.GaussianSpace

namespace BooleanAnalysis.GaussianSpace
open MeasureTheory ProbabilityTheory Filter
open ThresholdFunctions
open scoped BigOperators ENNReal NNReal Topology
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
/-- A unit-square-mass entropy bound from noise-energy deficits extends to
all functions with a strong Gaussian L² generator limit.
[OD14, §11.1, Gaussian Log-Sobolev inequality]
**Proof sketch.** At zero square mass the input vanishes almost everywhere.
Otherwise divide the input by the square root of its mass, scale its energy
deficit limit, apply the normalized bound, and rescale the entropy integral. -/
lemma gaussian_entropy_of_normalized_bound
    (hN : ∀ {F : (Fin n → ℝ) → ℝ} {D : ℝ}, MemLp F 2 γ →
      (∫ x, F x ^ 2 ∂γ) = 1 →
      Tendsto (fun t : ℝ => (1 - ∫ x, (gaussianNoise (Real.exp (-t)) F x) ^ 2 ∂γ) / t)
        (𝓝[>] (0 : ℝ)) (𝓝 D) →
      Integrable (fun x => F x ^ 2 * Real.log (F x ^ 2)) γ ∧
        (∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂γ) ≤ D)
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ)
    (hlim : Tendsto (fun t : ℝ => eLpNorm
      (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x) 2 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) γ ∧
      (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂γ) -
        (∫ x, f x ^ 2 ∂γ) * Real.log (∫ x, f x ^ 2 ∂γ) ≤
          2 * ∫ x, f x * g x ∂γ := by
  let A := ∫ x, f x ^ 2 ∂γ
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  by_cases hz : A = 0
  · have hsq := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hf.integrable_sq).mp hz
    have hlog : (fun x => f x ^ 2 * Real.log (f x ^ 2)) =ᵐ[γ] 0 := by
      filter_upwards [hsq] with x hx
      simp only [hx, zero_mul, Pi.zero_apply]
    have hfg : (fun x => f x * g x) =ᵐ[γ] 0 := by
      filter_upwards [hsq] with x hx
      have hfx : f x = 0 := sq_eq_zero_iff.mp hx
      simp only [hfx, zero_mul, Pi.zero_apply]
    refine ⟨(integrable_congr hlog).mpr (integrable_zero _ _ _), ?_⟩
    rw [integral_congr_ae hlog, integral_congr_ae hfg]
    simp only [Pi.zero_apply, integral_zero]
    change 0 - A * Real.log A ≤ 2 * 0
    simp only [hz, zero_mul, mul_zero, sub_zero, le_refl]
  · have hA : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hz)
    let F := fun x => f x / Real.sqrt A
    have hFsq (x) : F x ^ 2 = f x ^ 2 / A := by
      simp only [F, div_pow, Real.sq_sqrt hA.le]
    have hF : MemLp F 2 γ := by
      convert hf.const_smul (Real.sqrt A)⁻¹ using 1
      ext x
      change f x / Real.sqrt A = (Real.sqrt A)⁻¹ * f x
      ring
    have hFm : (∫ x, F x ^ 2 ∂γ) = 1 := by
      simp_rw [hFsq]
      rw [integral_div]
      exact div_self hz
    have hFnoise (ρ : ℝ) (x) : gaussianNoise ρ F x = gaussianNoise ρ f x / Real.sqrt A := by
      have hh := gaussianNoise_const_mul ρ (Real.sqrt A)⁻¹ f
      simpa only [F, div_eq_mul_inv, mul_comm] using congrFun hh x
    have hd := (tendsto_gaussianNoise_energy_deficit_of_strong_limit hf hg hlim).div_const A
    have hdF : Tendsto
        (fun t : ℝ => (1 - ∫ x, gaussianNoise (Real.exp (-t)) F x ^ 2 ∂γ) / t)
        (𝓝[>] (0 : ℝ)) (𝓝 ((2 * ∫ x, f x * g x ∂γ) / A)) := by
      apply hd.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      simp_rw [hFnoise, div_pow, Real.sq_sqrt hA.le]
      rw [integral_div]
      change ((A - ∫ x, gaussianNoise (Real.exp (-t)) f x ^ 2 ∂γ) / t) / A = _
      field_simp [hz, ht.ne']
    have hn := hN hF hFm hdF
    have hnorm : Integrable (fun x => (f x ^ 2 / A) * Real.log (f x ^ 2 / A)) γ := by
      simpa only [hFsq] using hn.1
    obtain ⟨hi, he⟩ := integral_mul_log_rescale hf.integrable_sq hA hnorm
    refine ⟨hi, ?_⟩
    rw [he]
    change A * (∫ x, (f x ^ 2 / A) * Real.log (f x ^ 2 / A) ∂γ) ≤ _
    have hni : (∫ x, (f x ^ 2 / A) * Real.log (f x ^ 2 / A) ∂γ) ≤
        (2 * ∫ x, f x * g x ∂γ) / A := by simpa only [hFsq] using hn.2
    calc
      _ ≤ A * ((2 * ∫ x, f x * g x ∂γ) / A) := mul_le_mul_of_nonneg_left hni hA.le
      _ = _ := by field_simp [hz]

end BooleanAnalysis.GaussianSpace

namespace BooleanAnalysis.GaussianSpace
open MeasureTheory Filter
open ThresholdFunctions
open scoped ENNReal Topology
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- Every strong Gaussian L² generator limit satisfies Gaussian log-Sobolev,
including integrability of its squared-input entropy integrand.
[OD14, §11.1, Gaussian Log-Sobolev inequality]
**Proof sketch.** The strong limit determines the noise-energy deficit.
Hypercontractivity and power-secant Fatou bounds prove the normalized
inequality, and positive mass rescaling gives the general statement. -/
lemma gaussian_entropy_of_strong_limit
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ)
    (hlim : Tendsto (fun t : ℝ => eLpNorm
      (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x) 2 γ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) γ ∧
      (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂γ) -
        (∫ x, f x ^ 2 ∂γ) * Real.log (∫ x, f x ^ 2 ∂γ) ≤
          2 * ∫ x, f x * g x ∂γ := (by
    exact gaussian_entropy_of_normalized_bound
      (fun {F} {D} hF hmass hD =>
        gaussian_entropy_normalized_of_energy_deficit hF hmass hD)
      hf hg hlim
)

end BooleanAnalysis.GaussianSpace
