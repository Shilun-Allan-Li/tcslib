/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Fourier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Characteristic limits for correlated Boolean blocks

## Main definitions

* `correlatedSignCharacteristic`: the real characteristic function of one
  correlated pair of uniform signs.

## Main results

Scalar cosine asymptotics give the Gaussian characteristic limit for normalized
blocks of independent correlated sign pairs.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, BitsToGaussians and Gaussian Hypercontractivity.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- The characteristic function of a pair of uniform signs with correlation
`ρ ∈ [-1,1]`, at the two real frequencies `a,b`.
[OD14, §11.1, BitsToGaussians]
The formula is defined for every real `ρ`; only valid correlations describe laws. -/
noncomputable def correlatedSignCharacteristic (ρ a b : ℝ) : ℝ :=
  (1 + ρ) / 2 * Real.cos (a + b) + (1 - ρ) / 2 * Real.cos (a - b)

/-- The cosine's quadratic remainder factors through the continuous sinc function.
This identity supplies the second-order characteristic asymptotics. -/
private lemma cos_sub_one_eq_sinc (t : ℝ) :
    Real.cos t - 1 = -(t ^ 2 / 2) * Real.sinc (t / 2) ^ 2 := by
  have hs (u : ℝ) : Real.sin u = u * Real.sinc u := by
    by_cases hu : u = 0
    · simp [hu]
    · rw [Real.sinc_of_ne_zero hu, mul_div_cancel₀ _ hu]
  have hc := Real.cos_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hc
  calc
    Real.cos t - 1 = -2 * Real.sin (t / 2) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
    _ = _ := by rw [hs]; ring

/-- The quadratic cosine term of a normalized block converges to minus half
the squared frequency. [OD14, §11.1, BitsToGaussians]

**Proof sketch.** Factor the cosine remainder as a square of sinc. The normalized
argument tends to zero, sinc tends to one, and the Gaussian normalization cancels. -/
lemma tendsto_nat_mul_cos_div_sqrt_sub_one (a : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) * (Real.cos (a / Real.sqrt m) - 1))
      atTop (𝓝 (-(a ^ 2 / 2))) := by
  have ht : Tendsto (fun m : ℕ => a / (2 * Real.sqrt m)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt.const_mul (a / 2)
    convert h using 1
    · funext m
      rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
      ring
    · simp
  have hl := (((Real.continuous_sinc.tendsto 0).comp ht).pow 2).const_mul (-(a ^ 2 / 2))
  simp only [Real.sinc_zero, one_pow, mul_one] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Function.comp_apply]
  rw [cos_sub_one_eq_sinc, div_pow, Real.sq_sqrt (Nat.cast_nonneg m),
    show (a / Real.sqrt m) / 2 = a / (2 * Real.sqrt m) by ring]
  field_simp

/-- The one-bit characteristic function has the Gaussian quadratic term after
normalization. [OD14, §11.1, BitsToGaussians]

**Proof sketch.** Express the correlated sign pair as a mixture of equal and
opposite signs and apply the cosine limit to their two frequencies. -/
lemma tendsto_nat_mul_correlatedSignCharacteristic_sub_one (ρ a b : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) *
      (correlatedSignCharacteristic ρ (a / Real.sqrt m) (b / Real.sqrt m) - 1))
      atTop (𝓝 (-(a ^ 2 + b ^ 2 + 2 * ρ * a * b) / 2)) := by
  have h := ((tendsto_nat_mul_cos_div_sqrt_sub_one (a + b)).const_mul ((1 + ρ) / 2)).add
    ((tendsto_nat_mul_cos_div_sqrt_sub_one (a - b)).const_mul ((1 - ρ) / 2))
  convert h using 1
  · funext m
    simp only [correlatedSignCharacteristic, ← add_div, ← sub_div]
    ring
  · congr 1
    ring

/-- Normalized independent correlated Boolean blocks have the characteristic
function of a correlated Gaussian pair in the limit.
[OD14, §11.1, BitsToGaussians]

**Proof sketch.** Independence raises the one-bit characteristic to the block
size. Its first-order perturbation of one has the Gaussian quadratic limit, so
the standard exponential power limit applies. -/
lemma tendsto_correlatedSignCharacteristic_pow (ρ a b : ℝ) :
    Tendsto (fun m : ℕ =>
      correlatedSignCharacteristic ρ (a / Real.sqrt m) (b / Real.sqrt m) ^ m)
      atTop (𝓝 (Real.exp (-(a ^ 2 + b ^ 2 + 2 * ρ * a * b) / 2))) := by
  have h := Real.tendsto_one_add_pow_exp_of_tendsto
    (tendsto_nat_mul_correlatedSignCharacteristic_sub_one ρ a b)
  convert h using 1
  funext m
  congr 1
  ring

/-- The joint Fourier transform of a correlated Gaussian pair is the Gaussian
exponential with the corresponding covariance quadratic form.
[OD14, §11.1, Fact 11.7 and BitsToGaussians]

**Proof sketch.** Pull the phase back to the independent Gaussian inputs and
factor it into two scalar phases. Their known Gaussian Fourier integrals multiply;
the noise variance identity simplifies the resulting quadratic form. -/
lemma integral_exp_correlatedGaussianMeasure {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (a b : Fin n → ℝ) :
    (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
      Complex.exp (((∑ i, (a i * z.1 i + b i * z.2 i) : ℝ) : ℂ) * Complex.I)
        ∂correlatedGaussianMeasure ρ) =
      Complex.exp (-((∑ i, (a i ^ 2 + b i ^ 2 + 2 * ρ * a i * b i) : ℝ) : ℂ) / 2) := by
  let s := Real.sqrt (1 - ρ ^ 2)
  have hs : s ^ 2 + ρ ^ 2 = 1 := by
    dsimp [s]
    rw [Real.sq_sqrt (show 0 ≤ 1 - ρ ^ 2 by nlinarith [hρ.1, hρ.2])]
    ring
  have he (z : (Fin n → ℝ) × (Fin n → ℝ)) :
      (∑ i, (a i * z.1 i + b i * (ρ * z.1 i + s * z.2 i))) =
        (∑ i, (a i + ρ * b i) * z.1 i) + ∑ i, (s * b i) * z.2 i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold correlatedGaussianMeasure
  rw [integral_map_of_stronglyMeasurable (by fun_prop)
    ((by fun_prop : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      Complex.exp (((∑ i, (a i * z.1 i + b i * z.2 i) : ℝ) : ℂ) * Complex.I))).stronglyMeasurable)]
  change (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
    Complex.exp (((∑ i, (a i * z.1 i + b i * (ρ * z.1 i + s * z.2 i)) : ℝ) : ℂ) *
      Complex.I) ∂(γ).prod γ) = _
  have hphase (z : (Fin n → ℝ) × (Fin n → ℝ)) :
      Complex.exp (((∑ i, (a i * z.1 i + b i * (ρ * z.1 i + s * z.2 i)) : ℝ) : ℂ) *
        Complex.I) =
      Complex.exp (((∑ i, (a i + ρ * b i) * z.1 i : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((∑ i, (s * b i) * z.2 i : ℝ) : ℂ) * Complex.I) := by
    rw [he, Complex.ofReal_add, add_mul, Complex.exp_add]
  simp_rw [hphase]
  rw [integral_prod_mul
    (fun x : Fin n → ℝ => Complex.exp (((∑ i, (a i + ρ * b i) * x i : ℝ) : ℂ) * Complex.I))
    (fun y : Fin n → ℝ => Complex.exp (((∑ i, (s * b i) * y i : ℝ) : ℂ) * Complex.I)),
    integral_exp_mul_I_gaussianPi, integral_exp_mul_I_gaussianPi,
    ← Complex.exp_add]
  congr 1
  rw [← add_div, ← neg_add, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  linear_combination (b i) ^ 2 * hs

end BooleanAnalysis.GaussianSpace
