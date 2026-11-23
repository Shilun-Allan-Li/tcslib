/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.InvarianceExtensions
import TCSlib.BooleanAnalysis.GaussianSpace.ProductDensity
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Basic
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Distribution
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Interpolation
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Remez
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Exponential
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.WeightedRemez
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Laplace
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.LogConcaveEnvelope
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.LogConcave
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.PolynomialRestriction
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Multilinear
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Normalization
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.ExponentialNeedle
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.UniformNeedle
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.AffineNeedle
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization
import Mathlib.Algebra.MvPolynomial.Degrees

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian polynomial anticoncentration and CDF invariance

## Contents

* `Anticoncentration.Basic`: shared factorial and power estimates.

* `Anticoncentration.Distribution`: CDF comparison, smoothing, and power balancing.
* `Anticoncentration.Interpolation`: factorial-preserving polynomial interpolation bounds.
* `Anticoncentration.Remez`: measured node selection and univariate Remez estimates.
* `Anticoncentration.Exponential`: exponential mass, initial volumes, and polynomial moments.
* `Anticoncentration.WeightedRemez`: weighted Remez and one-dimensional small-ball estimates.
* `Anticoncentration.Laplace`: whole-line Laplace polynomial small-ball estimates.
* `Anticoncentration.LogConcaveEnvelope`: exponential bounds for log-concave densities.
* `Anticoncentration.LogConcave`: polynomial small-ball bounds for log-concave densities.
* `Anticoncentration.PolynomialRestriction`: degree bounds for affine line restrictions.
* `Anticoncentration.Multilinear`: polynomial representations and Gaussian moments of Fourier extensions.
* `Anticoncentration.Normalization`: transferring normalized polynomial bounds to intervals.
* `Anticoncentration.ExponentialNeedle`: normalized finite exponential interval estimates.
* `Anticoncentration.UniformNeedle`: normalized uniform interval estimates.
* `Anticoncentration.AffineNeedle`: affine exponential interval estimates.
* `Anticoncentration.Localization`: analytic foundations for localization.

## Main definitions

Arbitrary polynomials use Mathlib's `MvPolynomial`; multilinear Fourier extensions
reuse `fourierCoeff` and `evalMultilinearRV`. Kolmogorov distance is reused.

## Main results

Carbery–Wright and CDF invariance (Theorem 11.71), both with universal constants.
Log-concave localization supplies polynomial anticoncentration; fourth-order
invariance and the distributional smoothing estimates give the CDF comparison.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Carbery–Wright Theorem and Theorem 11.71.
* [CW01] A. Carbery and J. Wright, Distributional and Lq norm inequalities for
  polynomials over convex bodies in Rn, Mathematical Research Letters 8 (2001),
  233–248, Theorem 8.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

/-- A Gaussian polynomial of second moment one has small-ball probability at
most a universal constant times `k ε^(1/k)`. [OD14, §11.6; CW01, Thm. 8]
The polynomial may contain arbitrary powers, so the existing multilinear type
would be insufficient. Positive degree excludes division by zero in the exponent.

**Proof sketch.** Apply the Carbery–Wright log-concave polynomial inequality to
the standard product Gaussian measure and normalize by the second moment. -/
theorem carbery_wright :
    ∃ K : ℝ, 0 < K ∧ ∀ {n k : ℕ}, 1 ≤ k →
      ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ k →
      (∫ z : Fin n → ℝ, (MvPolynomial.eval z p) ^ 2
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) = 1 →
      ∀ ε : ℝ, 0 < ε →
        ((Measure.pi fun _ : Fin n => standardGaussianMeasure)
          {z | |MvPolynomial.eval z p| ≤ ε}).toReal ≤
          K * (k : ℝ) * ε ^ (1 / (k : ℝ)) := (by
  classical
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    rw [standardGaussianMeasure_eq]
    infer_instance
  refine ⟨4096 * Real.exp 6, by positivity, ?_⟩
  intro n k hk p hp hpnorm ε hε
  have hdrop (m : ℕ) :
      MeasurePreserving (fun x : Fin (m + 1) → ℝ => fun i : Fin m => x i.succ)
        (Measure.pi fun _ : Fin (m + 1) => standardGaussianMeasure)
        (Measure.pi fun _ : Fin m => standardGaussianMeasure) := by
    convert measurePreserving_snd.comp
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => standardGaussianMeasure) 0) using 1
  let tail := fun x : Fin (n + 2) → ℝ => fun i : Fin n => x i.succ.succ
  have htail : MeasurePreserving tail
      (Measure.pi fun _ : Fin (n + 2) => standardGaussianMeasure)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    (hdrop n).comp (hdrop (n + 1))
  let q : MvPolynomial (Fin (n + 2)) ℝ :=
    MvPolynomial.rename (fun i : Fin n => i.succ.succ) p
  have hq (x : Fin (n + 2) → ℝ) :
      MvPolynomial.eval x q = MvPolynomial.eval (tail x) p :=
    MvPolynomial.eval_rename _ _ _
  let ρ := fun x : Fin (n + 2) → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)
  have hρpos (x : Fin (n + 2) → ℝ) : 0 < ρ x :=
    Finset.prod_pos fun i _ => gaussianPDFReal_pos _ _ _ (by norm_num)
  have hρcont : Continuous ρ := by
    apply continuous_finset_prod
    intro i hi
    rw [gaussianPDFReal_def]
    fun_prop
  have hden (f : (Fin (n + 2) → ℝ) → ℝ) :
      (∫ x, f x ∂(Measure.pi fun _ : Fin (n + 2) => standardGaussianMeasure)) =
        ∫ x, ρ x * f x := by
    simpa only [standardGaussianMeasure_eq, smul_eq_mul] using
      integral_pi_gaussianReal_eq_integral_smul (fun _ : Fin (n + 2) => 0) 1
        (by norm_num) f
  have htrans (f : (Fin n → ℝ) → ℝ) (hf : StronglyMeasurable f) :
      (∫ x, f (tail x) ∂(Measure.pi fun _ : Fin (n + 2) => standardGaussianMeasure)) =
        ∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
    have h := integral_map_of_stronglyMeasurable
      (μ := Measure.pi fun _ : Fin (n + 2) => standardGaussianMeasure) htail.measurable hf
    rw [htail.map_eq] at h
    exact h.symm
  have hρnorm : (∫ x, ρ x) = 1 := by
    simpa only [mul_one, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
      (hden (fun _ => 1)).symm
  have hqnorm : (∫ x, MvPolynomial.eval x q ^ 2 * ρ x) = 1 := by
    have h := htrans (fun x => MvPolynomial.eval x p ^ 2)
      ((MvPolynomial.continuous_eval p).pow 2).stronglyMeasurable
    rw [hpnorm] at h
    rw [hden] at h
    simpa only [← hq, mul_comm] using h
  have hsmall := PolynomialAnticoncentration.Localization.log_concave_integral_smallBall_le_of_integral_sq_eq_one
    (n := n + 1) (by omega) ρ hρcont hρpos
    (concaveOn_log_prod_gaussianPDFReal (fun _ => 0) 1 (by norm_num))
    hρnorm q k ((MvPolynomial.totalDegree_rename_le _ p).trans hp) hk hqnorm ε hε
  let A := {x : Fin n → ℝ | |MvPolynomial.eval x p| ≤ ε}
  let B := {x : Fin (n + 2) → ℝ | |MvPolynomial.eval x q| ≤ ε}
  have hA : MeasurableSet A :=
    (isClosed_le (MvPolynomial.continuous_eval p).abs continuous_const).measurableSet
  have hB : MeasurableSet B :=
    (isClosed_le (MvPolynomial.continuous_eval q).abs continuous_const).measurableSet
  have hmass : (∫ x in B, ρ x) =
      ((Measure.pi fun _ : Fin (n + 2) => standardGaussianMeasure) B).toReal := by
    rw [← integral_indicator hB]
    calc
      _ = ∫ x, ρ x * B.indicator (fun _ => (1 : ℝ)) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ B
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
      _ = _ := by
        rw [← hden, integral_indicator hB, setIntegral_const]
        simp only [smul_eq_mul, mul_one, measureReal_def]
  have hpre : tail ⁻¹' A = B := by
    ext x
    change |MvPolynomial.eval (tail x) p| ≤ ε ↔ |MvPolynomial.eval x q| ≤ ε
    rw [hq]
  have hm := htail.measure_preimage hA.nullMeasurableSet
  rw [hpre] at hm
  change ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal ≤ _
  rw [← hm, ← hmass]
  exact hsmall
)


/-- A variance-one multilinear function with small influences has close Boolean
and Gaussian CDFs, with error `K k ε^(1/(4k+1))`. [OD14, Thm. 11.71]
The variance hypothesis is equality, as in the source.

**Proof sketch.** Compare smoothed half-line tests using fourth-order invariance,
then apply Carbery–Wright to the centered Gaussian polynomial to control the
boundary intervals. Optimize the smoothing width to obtain the exponent. -/
theorem invariance_cdf :
    ∃ K : ℝ, 0 < K ∧ ∀ {n k : ℕ}, 1 ≤ k → ∀ f : BooleanFunc n,
      has_degree_at_most f k → cubeVariance f = 1 →
      ∀ ε : ℝ, 0 ≤ ε → (∀ i, influence i f ≤ ε) →
        kolmogorovDistance
          ((Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure).map f)
          ((Measure.pi fun _ : Fin n => standardGaussianMeasure).map
            (evalMultilinearRV (fourierCoeff f) (fun i z => z i))) ≤
          K * (k : ℝ) * ε ^ (1 / (4 * (k : ℝ) + 1)) := (by
  classical
  obtain ⟨Kcw, hKcw, hCW⟩ := carbery_wright
  refine ⟨2 * (5 * Kcw + 1), by positivity, ?_⟩
  intro n k hk f hdegree hvar ε hε hinf
  letI : IsProbabilityMeasure standardGaussianMeasure :=
    hasInvarianceMoments_standardGaussian.reasonable.probability
  let β : Measure (BoolCube n) :=
    Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure
  let γ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  let Q := evalMultilinearRV (fourierCoeff f) (fun i (z : Fin n → ℝ) => z i)
  have hdegreeF : MultilinearPolynomial.HasDegreeAtMost (fourierCoeff f) k := by
    intro S hS
    by_contra hne
    exact (not_le_of_gt hS) (hdegree S hne)
  obtain ⟨p, hp, hpQ⟩ :=
    PolynomialAnticoncentration.exists_mvPolynomial_eval_eq_evalMultilinearRV
      (fourierCoeff f) hdegreeF
  have heq : (fun z => MvPolynomial.eval z p) = Q := funext hpQ
  have hQ : Measurable Q := heq ▸ (MvPolynomial.continuous_eval p).measurable
  let μ := β.map f
  let ν := γ.map Q
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_of_finite f).aemeasurable
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hQ.aemeasurable
  have hIX : iIndepFun (fun (i : Fin n) (x : BoolCube n) => boolToSign (x i)) β :=
    iIndepFun_pi (μ := fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
      (X := fun _ => boolToSign) (fun _ => (measurable_of_finite boolToSign).aemeasurable)
  have hIY : iIndepFun (fun (i : Fin n) (z : Fin n → ℝ) => z i) γ :=
    iIndepFun_pi (μ := fun _ : Fin n => standardGaussianMeasure)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have heval : evalMultilinearRV (fourierCoeff f)
      (fun (i : Fin n) (x : BoolCube n) => boolToSign (x i)) = f := by
    change MultilinearPolynomial.eval (fourierCoeff f) = f
    exact MultilinearPolynomial.eval_fourierCoeff f
  -- Compare smooth tests using fourth-order invariance.
  have herror (φ : ℝ → ℝ) (hφ : ContDiff ℝ 4 φ)
      (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ t, |iteratedDeriv 4 φ t| ≤ C) :
      |(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν| ≤ C * ((16 : ℝ) ^ k * ε / 8) := by
    have h := invariance_small_influences (μ := β) (ν := γ) (fourierCoeff f) hdegreeF
      (by simpa only [MultilinearPolynomial.eval_fourierCoeff] using hvar.le) ε hε
      (by simpa only [MultilinearPolynomial.eval_fourierCoeff] using hinf)
      (fun (i : Fin n) (x : BoolCube n) => boolToSign (x i))
      (fun (i : Fin n) (z : Fin n → ℝ) => z i) hIX hIY
      (fun i => hasInvarianceMoments_uniformBoolCoordinate i)
      (fun i => hasInvarianceMoments_gaussianCoordinate i) φ hφ C hC0 hC
    change |(∫ x, φ x ∂β.map f) - ∫ x, φ x ∂γ.map Q| ≤ _
    rw [integral_map_of_stronglyMeasurable (measurable_of_finite f) hφ.continuous.stronglyMeasurable,
      integral_map_of_stronglyMeasurable hQ hφ.continuous.stronglyMeasurable]
    rw [heval] at h
    apply h.trans
    have hnum := mul_le_mul_of_nonneg_right (degree_mul_nine_pow_le_sixteen_pow k) hε
    have hnonneg : 0 ≤ (16 : ℝ) ^ k * ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hnum hC0]
  -- Variance one controls the second moment about every interval endpoint.
  have hinterval (w : ℝ) (hw : 0 < w) (u : ℝ) :
      (ν (Set.Ioc u (u + w))).toReal ≤ Kcw * (k : ℝ) * w ^ (1 / (k : ℝ)) := by
    have hmoment := PolynomialAnticoncentration.integral_sq_sub_evalMultilinearRV_gaussian_eq_cubeVariance_add_sq
      (fourierCoeff f) u
    rw [MultilinearPolynomial.eval_fourierCoeff, hvar] at hmoment
    have hlower : 1 ≤ ∫ z : Fin n → ℝ, (MvPolynomial.eval z p - u) ^ 2 ∂γ := by
      simp_rw [hpQ]
      exact hmoment.symm ▸ le_add_of_nonneg_right (sq_nonneg _)
    have h := PolynomialAnticoncentration.measure_map_Ioc_le_of_normalized_smallBall_bound
      γ k Kcw (hCW hk) p hp u hlower w hw
    simpa only [heq] using h
  have hbound := Invariance.kolmogorov_bound_of_fourth_derivative μ ν k hk
    (Kcw * (k : ℝ)) ((16 : ℝ) ^ k * ε / 8) (by positivity) (by positivity)
    herror hinterval
  change kolmogorovDistance μ ν ≤ _
  apply hbound.trans
  -- Taking the smoothing root absorbs the exponential degree factor.
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by positivity
  have h5 : (5 : ℝ) ^ (1 / (k : ℝ)) ≤ 5 := by
    calc
      _ ≤ (5 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) ((div_le_one hkpos).2 hkR)
      _ = 5 := Real.rpow_one _
  have h16 : ((16 : ℝ) ^ k) ^ (1 / (4 * (k : ℝ) + 1)) ≤ 2 := by
    calc
      _ = (2 : ℝ) ^ ((4 * (k : ℝ)) / (4 * (k : ℝ) + 1)) := by
        rw [show (16 : ℝ) ^ k = 2 ^ (4 * k) by rw [pow_mul]; norm_num,
          ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
        push_cast
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          ((div_le_one (by positivity : (0 : ℝ) < 4 * (k : ℝ) + 1)).2 (by linarith))
      _ = 2 := Real.rpow_one _
  rw [show (8 : ℝ) * (16 ^ k * ε / 8) = 16 ^ k * ε by ring,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Real.mul_rpow (by positivity) hε]
  have hcoeff : Kcw * (k : ℝ) * (5 : ℝ) ^ (1 / (k : ℝ)) + 1 ≤
      (5 * Kcw + 1) * (k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left h5 (show 0 ≤ Kcw * (k : ℝ) by positivity)]
  calc
    _ ≤ ((5 * Kcw + 1) * (k : ℝ)) *
        (2 * ε ^ (1 / (4 * (k : ℝ) + 1))) :=
      mul_le_mul hcoeff
        (mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg hε _))
        (by positivity) (by positivity)
    _ = _ := by ring
)


end BooleanAnalysis.GaussianSpace
