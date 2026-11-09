/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.LpBounds
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Kernel

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Dual tests for Gaussian hypercontractivity

## Main definitions

The Gaussian noise operator, its joint coupling and the existing Lp pairing bound are reused.

## Main results

* `gaussianNoise_dual_test_bound`: bounded tests have the sharp conjugate-exponent bound.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Theorem 11.23.
-/

open MeasureTheory
open scoped ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => Measure.pi (fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))

/-- Gaussian averaging satisfies the conjugate-exponent bound against every
bounded test function at the finite hypercontractivity threshold.
[OD14, §11.1, Theorem 11.23]

**Proof sketch.** Set the two pairing offsets to `p-1` and `1/(q-1)`.
The positive-offset inequality bounds the correlated product, and Fubini
identifies that product with the test against the Gaussian average. -/
lemma gaussianNoise_dual_test_bound (p q ρ : ℝ) (hp : 1 < p) (hpq : p ≤ q)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρ : ρ ^ 2 * (q - 1) ≤ p - 1)
    (hfst : MeasurePreserving Prod.fst (correlatedGaussianMeasure ρ) γ)
    (hsnd : MeasurePreserving Prod.snd (correlatedGaussianMeasure ρ) γ)
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f (ENNReal.ofReal p) γ)
    (hg : MemLp g ⊤ γ) :
    |∫ x, gaussianNoise ρ f x * g x ∂γ| ≤
      (eLpNorm f (ENNReal.ofReal p) γ).toReal *
        (eLpNorm g (ENNReal.ofReal (q / (q - 1))) γ).toReal := by
  have hq : 0 < q - 1 := by linarith
  have hdual : 1 + (q - 1)⁻¹ = q / (q - 1) := by
    field_simp [hq.ne']
    ring
  have hp' : 1 + (p - 1) = p := by ring
  have hrs : (q - 1)⁻¹ * (p - 1) ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_one hq]
    linarith
  have hc : ρ ^ 2 ≤ (q - 1)⁻¹ * (p - 1) := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hq).mpr hρ
  have hgp : MemLp g (ENNReal.ofReal (1 + (q - 1)⁻¹)) γ := hg.mono_exponent le_top
  have hfp : MemLp f (ENNReal.ofReal (1 + (p - 1))) γ := by rwa [hp']
  obtain ⟨hi, hb⟩ := gaussian_two_function_positiveOffsets (q - 1)⁻¹ (p - 1) ρ
    (inv_pos.mpr hq) (sub_pos.mpr hp) hrs hρ0 hρ1 hc hfst hsnd hgp hfp
  calc
    _ = |∫ z, g z.1 * f z.2 ∂correlatedGaussianMeasure ρ| := by
      rw [integral_correlatedGaussianMeasure_of_integrable ρ hi]
      simp only [mul_comm]
    _ ≤ ∫ z, |g z.1| * |f z.2| ∂correlatedGaussianMeasure ρ := by
      simpa only [abs_mul] using (abs_integral_le_integral_abs
        (f := fun z => g z.1 * f z.2) (μ := correlatedGaussianMeasure ρ))
    _ ≤ _ := by simpa only [hdual, hp', mul_comm] using hb

end BooleanAnalysis.GaussianSpace
