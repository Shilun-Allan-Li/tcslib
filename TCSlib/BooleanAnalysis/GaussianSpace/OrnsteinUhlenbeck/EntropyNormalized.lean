/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck.EntropyScalar
import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian entropy at unit square mass

## Main definitions

The Gaussian noise operator and its hypercontractive exponent are reused.

## Main results

* `gaussianNoise_sq_integral_le_power_moment`: hypercontractivity controls
  Gaussian noise energy by a lower power moment.
* `gaussian_entropy_normalized_of_energy_deficit`: a finite noise-energy
  deficit limit bounds entropy and proves integrability at unit square mass.

The exponent approaches two from below. Power secants and Fatou's inequality
handle the entropy limit, including inputs whose entropy is not yet known finite.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian Log-Sobolev inequality.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace BooleanAnalysis.GaussianSpace
/-- The integral of a positive power of the norm equals the corresponding
power of the finite Lp seminorm. -/
lemma integral_norm_rpow_eq_toReal_eLpNorm_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫ x, ‖f x‖ ^ p ∂μ) = (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p := by
  have hm : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [hf.eLpNorm_eq_integral_rpow_norm (by simpa using hp) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hm _), ← Real.rpow_mul hm,
    inv_mul_cancel₀ hp.ne', Real.rpow_one]
open ThresholdFunctions
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
/-- For a Gaussian L² function of square integral one, the squared norm of
its noisy average is bounded by its square moment of exponent (1+ρ²)/2.
[OD14, §11.1, Gaussian hypercontractivity]
**Proof sketch.** Apply hypercontractivity from exponent 1+ρ² to exponent two.
The input seminorm is at most one, so decreasing its outer power enlarges the
bound. Rewrite the resulting seminorm as a power moment. -/
lemma gaussianNoise_sq_integral_le_power_moment
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ)
    (hm : (∫ x, f x ^ 2 ∂γ) = 1) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, (gaussianNoise ρ f x) ^ 2 ∂γ) ≤
      ∫ x, (f x ^ 2) ^ ((1 + ρ ^ 2) / 2) ∂γ := by
  let p : ℝ := 1 + ρ ^ 2
  have hp1 : 1 ≤ p := by dsimp only [p]; nlinarith [sq_nonneg ρ]
  have hp0 : 0 < p := zero_lt_one.trans_le hp1
  have hp2 : p ≤ 2 := by dsimp only [p]; nlinarith [hρ.1, hρ.2]
  have hpe : ENNReal.ofReal p ≤ 2 := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp2
  have hfp : MemLp f (ENNReal.ofReal p) γ := hf.mono_exponent hpe
  have hnorm : eLpNorm f 2 γ = 1 := by
    rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, hm,
      Real.one_rpow, ENNReal.ofReal_one]
  have hpN : (eLpNorm f (ENNReal.ofReal p) γ).toReal ≤ 1 := by
    have hle := (eLpNorm_le_eLpNorm_of_exponent_le hpe hf.aestronglyMeasurable).trans_eq hnorm
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hle
  have hn := gaussian_hypercontractive (ENNReal.ofReal p) 2
    (by simpa using ENNReal.ofReal_le_ofReal hp1) hpe ρ hρ.1 hρ.2
    (by simp only [show (2 : ℝ≥0∞) - 1 = 1 by exact_mod_cast (ENNReal.natCast_sub 2 1).symm, mul_one]
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub p (show 0 ≤ (1 : ℝ) by norm_num)]
        simp only [p, add_sub_cancel_left, le_refl]) hfp
  have hN := ENNReal.toReal_mono hfp.eLpNorm_lt_top.ne hn.2
  have hsq := integral_norm_rpow_eq_toReal_eLpNorm_rpow (by norm_num : (0 : ℝ) < 2) (by simpa only [ENNReal.ofReal_ofNat] using hn.1)
  simp only [ENNReal.ofReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at hsq
  calc
    (∫ x, gaussianNoise ρ f x ^ 2 ∂γ) = (eLpNorm (gaussianNoise ρ f) 2 γ).toReal ^ 2 := hsq
    _ ≤ (eLpNorm f (ENNReal.ofReal p) γ).toReal ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hN 2
    _ ≤ (eLpNorm f (ENNReal.ofReal p) γ).toReal ^ p := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge_of_imp ENNReal.toReal_nonneg hpN hp2
        (fun _ h => False.elim (by norm_num at h))
    _ = ∫ x, ‖f x‖ ^ p ∂γ := (integral_norm_rpow_eq_toReal_eLpNorm_rpow hp0 hfp).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change |f x| ^ p = (f x ^ 2) ^ ((1 + ρ ^ 2) / 2)
        rw [← sq_abs (f x), ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg (f x))]
        congr 1
        dsimp only [p]
        ring

end BooleanAnalysis.GaussianSpace

open Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace

/-- The exponent offset used in Gaussian hypercontractivity lies between zero
and one at positive time. [OD14, §11.1, Gaussian Log-Sobolev differentiation] -/
lemma gaussian_entropy_exponent_pos_le_one {t : ℝ} (ht : 0 < t) :
    0 < (1 - Real.exp (-2*t))/2 ∧ (1 - Real.exp (-2*t))/2 ≤ 1 := by
  have hp := Real.exp_pos (-2*t)
  have hl : Real.exp (-2*t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  constructor <;> linarith

/-- The Gaussian hypercontractive exponent offset tends to zero through
positive values as time decreases to zero. [OD14, §11.1, Gaussian Log-Sobolev] -/
lemma tendsto_gaussian_entropy_exponent :
    Tendsto (fun t : ℝ => (1 - Real.exp (-2*t))/2)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun t : ℝ => (1 - Real.exp (-2*t))/2) := by fun_prop
    simpa only [mul_zero, Real.exp_zero, sub_self, zero_div] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (gaussian_entropy_exponent_pos_le_one ht).1

/-- Time divided by the Gaussian hypercontractive exponent offset tends to one
at time zero. [OD14, §11.1, Gaussian Log-Sobolev differentiation]
**Proof sketch.** The offset has derivative one at zero. Its difference
quotient tends to one, so the reciprocal quotient does as well. -/
lemma tendsto_time_div_gaussian_entropy_exponent :
    Tendsto (fun t : ℝ => t / ((1 - Real.exp (-2*t))/2))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hd : HasDerivAt (fun t : ℝ => (1 - Real.exp (-2*t))/2) 1 0 := by
    simpa using ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      (((hasDerivAt_id (0 : ℝ)).const_mul (-2)).exp)).div_const 2
  have hq : Tendsto (fun t : ℝ => ((1 - Real.exp (-2*t))/2)/t)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hh := hd.tendsto_slope_zero_right
    simp only [zero_add, mul_zero, Real.exp_zero, sub_self, zero_div,
      sub_zero, smul_eq_mul] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  simpa only [inv_div, inv_one] using hq.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

end BooleanAnalysis.GaussianSpace

namespace BooleanAnalysis.GaussianSpace
open MeasureTheory ProbabilityTheory Filter
open ThresholdFunctions
open scoped BigOperators ENNReal NNReal Topology
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- For a Gaussian square-integrable function of square integral one, a finite
right derivative of its noise energy deficit bounds its entropy and proves
entropy integrability. [OD14, §11.1, Gaussian Log-Sobolev]
**Proof sketch.** Hypercontractivity bounds the noise square integral by a
moment of exponent below two. Its normalized deficit controls the integral of
the corresponding power secant. Let positive times decrease to zero and apply
the entropy Fatou criterion; the exponent offset is asymptotic to time. -/
lemma gaussian_entropy_normalized_of_energy_deficit
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ)
    (hm : (∫ x, f x ^ 2 ∂γ) = 1) {D : ℝ}
    (hD : Tendsto (fun t : ℝ =>
      (1 - ∫ x, gaussianNoise (Real.exp (-t)) f x ^ 2 ∂γ) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 D)) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) γ ∧
      (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂γ) ≤ D := (by
    let t := fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)
    let ε := fun k => (1 - Real.exp (-2 * t k)) / 2
    have ht (k : ℕ) : 0 < t k := by dsimp [t]; positivity
    have htlim : Tendsto t atTop (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ht⟩
    have he0 (k : ℕ) : 0 < ε k := (gaussian_entropy_exponent_pos_le_one (ht k)).1
    have he1 (k : ℕ) : ε k ≤ 1 := (gaussian_entropy_exponent_pos_le_one (ht k)).2
    have helim : Tendsto ε atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_gaussian_entropy_exponent.comp htlim
    have hff : Integrable (fun x => f x ^ 2) γ := by
      simpa only [pow_two] using hf.integrable_mul hf
    have hmoment (k : ℕ) : Integrable (fun x => (f x ^ 2) ^ (1 - ε k)) γ := by
      let p := 2 * (1 - ε k)
      have hp : 0 ≤ p := by dsimp only [p]; nlinarith [he1 k]
      have hp2 : p ≤ 2 := by dsimp only [p]; nlinarith [he0 k]
      have hfp := hf.mono_exponent
        (show ENNReal.ofReal p ≤ 2 by simpa using ENNReal.ofReal_le_ofReal hp2)
      have hi : Integrable (fun x => |f x| ^ p) γ := by
        simpa only [ENNReal.toReal_ofReal hp, Real.norm_eq_abs] using hfp.integrable_norm_rpow'
      convert hi using 1
      funext x
      rw [← sq_abs (f x), ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg (f x))]
    have hQ (k : ℕ) : Integrable (fun x => (f x ^ 2 - (f x ^ 2) ^ (1 - ε k)) / ε k) γ :=
      (hff.sub (hmoment k)).div_const (ε k)
    let b := fun k => ((1 - ∫ x, gaussianNoise (Real.exp (-t k)) f x ^ 2 ∂γ) / t k) *
      (t k / ε k)
    have hb : Tendsto b atTop (𝓝 D) := by
      simpa only [mul_one] using (hD.comp htlim).mul (tendsto_time_div_gaussian_entropy_exponent.comp htlim)
    apply integrable_mul_log_of_power_secants (fun x => sq_nonneg _) (hf.aestronglyMeasurable.pow 2)
      he0 he1 helim hQ hb
    intro k
    have hρ : Real.exp (-t k) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (ht k).le)⟩
    have hsquare : Real.exp (-t k) ^ 2 = Real.exp (-2 * t k) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hexponent : (1 + Real.exp (-t k) ^ 2) / 2 = 1 - ε k := by
      rw [hsquare]
      dsimp only [ε]
      ring
    have hcontract := gaussianNoise_sq_integral_le_power_moment hf hm hρ
    rw [hexponent] at hcontract
    rw [integral_div, integral_sub hff (hmoment k), hm]
    calc
      (1 - ∫ x, (f x ^ 2) ^ (1 - ε k) ∂γ) / ε k ≤
          (1 - ∫ x, gaussianNoise (Real.exp (-t k)) f x ^ 2 ∂γ) / ε k :=
        div_le_div_of_nonneg_right (sub_le_sub_left hcontract 1) (he0 k).le
      _ = b k := by
        dsimp only [b]
        field_simp [(ht k).ne', (he0 k).ne']
)

end BooleanAnalysis.GaussianSpace
