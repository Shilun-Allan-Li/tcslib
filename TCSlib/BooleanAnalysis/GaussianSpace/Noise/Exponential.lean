/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian exponential envelopes

## Main definitions

The coordinate sum of absolute values supplies an exponential envelope for
Taylor approximations of Gaussian Fourier characters.

## Main results

* `integrable_exp_sum_abs_gaussian`: Gaussian exponential integrability.
* `memLp_exp_sum_abs_gaussian`: the same envelope belongs to every finite Lp.
* `tendsto_gaussian_exp_taylor`: exponential Taylor approximation in Gaussian Lp.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, proof of Theorem 11.22.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Every exponential of a multiple of the sum of absolute Gaussian coordinates
is integrable. [OD14, §11.1, proof of Thm. 11.22]

**Proof sketch.** Each scalar exponential is bounded by the sum of the two
Gaussian moment-generating functions. Factor the product over the coordinates. -/
lemma integrable_exp_sum_abs_gaussian (c : ℝ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (c * ∑ i, |x i|)) γ := by
  have hi (i : Fin n) :
      Integrable (fun y : ℝ => Real.exp (c * |y|)) standardGaussianMeasure :=
    integrable_exp_mul_abs (integrable_exp_mul_gaussianReal c)
      (integrable_exp_mul_gaussianReal (-c))
  convert Integrable.fintype_prod hi using 1
  funext x
  rw [Finset.mul_sum, Real.exp_sum]

/-- Gaussian exponential envelopes have every finite Lp norm.
[OD14, §11.1, proof of Thm. 11.22]

**Proof sketch.** Taking a finite power of the exponential only changes its
coefficient, so the integrability result applies at the requested exponent. -/
lemma memLp_exp_sum_abs_gaussian (c : ℝ) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun x : Fin n → ℝ => Real.exp (c * ∑ i, |x i|)) p γ := by
  by_cases hp0 : p = 0
  · subst p
    exact memLp_zero_iff_aestronglyMeasurable.mpr
      ((by fun_prop : Continuous (fun x : Fin n → ℝ =>
        Real.exp (c * ∑ i, |x i|))).aestronglyMeasurable)
  apply (integrable_norm_rpow_iff ((by fun_prop : Continuous (fun x : Fin n → ℝ =>
    Real.exp (c * ∑ i, |x i|))).aestronglyMeasurable) hp0 hp).mp
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul,
    mul_right_comm] using integrable_exp_sum_abs_gaussian (n := n) (c * p.toReal)

/-- An Lp envelope and pointwise convergence to zero imply convergence of the
finite Lp seminorms. This is the dominated-convergence step used below.

**Proof sketch.** Apply nonnegative dominated convergence to the p-th powers
of the norms, then use continuity of the positive p-th root. -/
private lemma tendsto_eLpNorm_zero_of_dominated {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    {F : ℕ → α → E} (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    {b : α → ℝ} (hb : MemLp b p μ)
    (hbound : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ ‖b x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (F k) p μ) atTop (𝓝 0) := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have ht : Tendsto (fun k => ∫⁻ x, ‖F k x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using tendsto_lintegral_of_dominated_convergence'
      (F := fun k x => ‖F k x‖ₑ ^ p.toReal) (f := fun _ => 0)
      (fun x => ‖b x‖ₑ ^ p.toReal)
      (fun k => (hF k).enorm.pow_const p.toReal)
      (fun k => (hbound k).mono fun x hx => ENNReal.rpow_le_rpow
        (enorm_le_iff_norm_le.mpr hx) ENNReal.toReal_nonneg)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hb.eLpNorm_lt_top).ne
      (hlim.mono fun x hx => by
        simpa only [enorm_zero, ENNReal.zero_rpow_of_pos hp'] using
          ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto (0 : ℝ≥0∞)).comp
            (by simpa only [enorm_zero] using hx.enorm))
  simp only [eLpNorm_eq_lintegral_rpow_enorm hp0 hp]
  simpa only [one_div, Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hp')] using
    ((ENNReal.continuous_rpow_const (y := p.toReal⁻¹)).tendsto (0 : ℝ≥0∞)).comp ht

/-- Taylor polynomials of a complex linear exponential converge in every finite
Gaussian Lp seminorm. [OD14, §11.1, proof of Thm. 11.22]

**Proof sketch.** The Taylor remainder is at most the exponential of the norm
of its argument. Bound that norm by the operator norm times the sum of absolute
coordinates and apply dominated convergence with the Gaussian exponential envelope. -/
lemma tendsto_gaussian_exp_taylor (L : (Fin n → ℝ) →L[ℝ] ℂ)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    Tendsto (fun k => eLpNorm (fun x : Fin n → ℝ => Complex.exp (L x) -
      ∑ m ∈ Finset.range k, (L x) ^ m / m.factorial) p γ) atTop (𝓝 0) := by
  by_cases hp0 : p = 0
  · simpa only [hp0, eLpNorm_exponent_zero] using tendsto_const_nhds
  apply tendsto_eLpNorm_zero_of_dominated hp0 hp
    (fun k => (by fun_prop : Continuous (fun x : Fin n → ℝ => Complex.exp (L x) -
      ∑ m ∈ Finset.range k, (L x) ^ m / m.factorial)).aestronglyMeasurable)
    (memLp_exp_sum_abs_gaussian ‖L‖ hp)
  · intro k
    filter_upwards [] with x
    have hx : ‖x‖ ≤ ∑ i, |x i| := by
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr
      intro i
      exact (Real.norm_eq_abs (x i)).le.trans (Finset.single_le_sum
        (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp ‖L x‖ - ∑ m ∈ Finset.range k, ‖L x‖ ^ m / m.factorial :=
        Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (L x) k
      _ ≤ Real.exp ‖L x‖ := sub_le_self _ (Finset.sum_nonneg fun _ _ => by positivity)
      _ ≤ _ := Real.exp_le_exp.mpr ((L.le_opNorm x).trans
        (mul_le_mul_of_nonneg_left hx (norm_nonneg L)))
  · filter_upwards [] with x
    have ht : Tendsto (fun k => ∑ m ∈ Finset.range k, (L x) ^ m / m.factorial)
        atTop (𝓝 (Complex.exp (L x))) := (L x).exp'.tendsto_limit
    simpa only [sub_self] using
      (tendsto_const_nhds (x := Complex.exp (L x))).sub ht

end BooleanAnalysis.GaussianSpace
