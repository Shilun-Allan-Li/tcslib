/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Perturbation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian stability under square-integrable perturbations

## Main definitions

The existing Gaussian noise stability and real L² norm are reused.

## Main results

* `gaussianNoiseStability_sub_le`: stability is two-Lipschitz on the L² unit ball.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, proof of (11.39).
-/

open MeasureTheory ProbabilityTheory
namespace BooleanAnalysis.GaussianSpace.MajorityIsStablest
open ThresholdFunctions Hypercontractivity
variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- Gaussian stability changes by at most twice the L² distance on the unit ball.
[OD14, §11.7, stability comparison after clipping]

**Proof sketch.** Split the quadratic difference into two pairings with the input
difference, using self-adjointness. Cauchy–Schwarz bounds each pairing, and
Gaussian noise contracts the L² norm. -/
theorem gaussianNoiseStability_sub_le {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {U V : (Fin n → ℝ) → ℝ} (hU : MemLp U 2 γ) (hV : MemLp V 2 γ)
    (hUn : rvLpNorm U γ 2 ≤ 1) (hVn : rvLpNorm V γ 2 ≤ 1) :
    |gaussianNoiseStability ρ U - gaussianNoiseStability ρ V| ≤
      2 * rvLpNorm (fun x => U x - V x) γ 2 := by
  have hTU := gaussianNoise_memLp hρ 2 (by norm_num) hU
  have hTV := gaussianNoise_memLp hρ 2 (by norm_num) hV
  have hD := hU.sub hV
  have hcs (A B : (Fin n → ℝ) → ℝ) (hA : MemLp A 2 γ) (hB : MemLp B 2 γ) :
      |∫ x, A x * B x ∂γ| ≤ rvLpNorm A γ 2 * rvLpNorm B γ 2 := by
    have heq : inner ℝ (hA.toLp A) (hB.toLp B) = ∫ x, A x * B x ∂γ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with x ha hb
      simp [ha, hb, RCLike.inner_apply, mul_comm]
    simpa only [heq, Lp.norm_toLp, rvLpNorm, ENNReal.ofReal_ofNat] using
      abs_real_inner_le_norm (hA.toLp A) (hB.toLp B)
  have hcontract (A : (Fin n → ℝ) → ℝ) (hA : MemLp A 2 γ) :
      rvLpNorm (gaussianNoise ρ A) γ 2 ≤ rvLpNorm A γ 2 := by
    simp only [rvLpNorm, ENNReal.ofReal_ofNat]
    exact ENNReal.toReal_mono hA.eLpNorm_lt_top.ne
      (gaussianNoise_contract hρ 2 (by norm_num) hA)
  have hsplit : gaussianNoiseStability ρ U - gaussianNoiseStability ρ V =
      (∫ x, (U x - V x) * gaussianNoise ρ U x ∂γ) +
        (∫ x, gaussianNoise ρ V x * (U x - V x) ∂γ) := by
    simp_rw [sub_mul, mul_sub]
    rw [integral_sub (f := fun x => U x * gaussianNoise ρ U x)
        (g := fun x => V x * gaussianNoise ρ U x)
        (hU.integrable_mul hTU) (hV.integrable_mul hTU),
      integral_sub (f := fun x => gaussianNoise ρ V x * U x)
        (g := fun x => gaussianNoise ρ V x * V x)
        (hTV.integrable_mul hU) (hTV.integrable_mul hV)]
    have hc := gaussianNoise_selfAdjoint hρ hV hU
    simp only [gaussianNoiseStability]
    have hv : (∫ x, gaussianNoise ρ V x * V x ∂γ) =
        ∫ x, V x * gaussianNoise ρ V x ∂γ := by
      congr 1
      funext x
      ring
    rw [hv]
    linarith
  rw [hsplit]
  calc
    _ ≤ |∫ x, (U x - V x) * gaussianNoise ρ U x ∂γ| +
        |∫ x, gaussianNoise ρ V x * (U x - V x) ∂γ| := abs_add_le _ _
    _ ≤ rvLpNorm (fun x => U x - V x) γ 2 * rvLpNorm (gaussianNoise ρ U) γ 2 +
        rvLpNorm (gaussianNoise ρ V) γ 2 * rvLpNorm (fun x => U x - V x) γ 2 :=
      add_le_add (hcs _ _ hD hTU) (hcs _ _ hTV hD)
    _ ≤ rvLpNorm (fun x => U x - V x) γ 2 * 1 +
        1 * rvLpNorm (fun x => U x - V x) γ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left ((hcontract U hU).trans hUn) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_right ((hcontract V hV).trans hVn) ENNReal.toReal_nonneg)
    _ = _ := by ring

end BooleanAnalysis.GaussianSpace.MajorityIsStablest
