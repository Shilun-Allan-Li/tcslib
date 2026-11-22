/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest.Bridge
import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest.Perturbation
import TCSlib.BooleanAnalysis.GaussianSpace.InvarianceExtensions
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Borell

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Clipping Gaussian extensions to the probability interval

## Main definitions

* `unitClip`: nearest-point clipping to the closed probability interval.

## Main results

Clipping squared is a bounded two-Lipschitz test, so Lipschitz invariance
controls the squared distance from a Gaussian extension to its clipping.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, proof of (11.39).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanAnalysis.GaussianSpace.MajorityIsStablest

open ThresholdFunctions Hypercontractivity

/-- Clipping a real number to the closed probability interval. [OD14, §11.7] -/
def unitClip (t : ℝ) : ℝ := min 1 (max 0 t)

/-- Clipping is the minimum of one and the maximum of zero and the input. -/
lemma unitClip_eq (t : ℝ) : unitClip t = min 1 (max 0 t) := rfl

/-- Every clipped value belongs to the closed probability interval. -/
lemma unitClip_mem (t : ℝ) : unitClip t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [unitClip_eq]
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- Clipping fixes every point of the closed probability interval. -/
lemma unitClip_eq_self {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : unitClip t = t := by
  rw [unitClip_eq, max_eq_right ht.1, min_eq_right ht.2]

/-- Clipping does not increase distances. [OD14, §11.7, clipping step] -/
lemma unitClip_lipschitz : LipschitzWith 1 unitClip := by
  exact (LipschitzWith.id.const_max 0).const_min 1

/-- Squared clipping is two-Lipschitz on the whole real line.
[OD14, §11.7, bounded test for the clipping error]

**Proof sketch.** Factor the difference of squares. The sum of two clipped
values is at most two, and clipping itself does not increase distances. -/
lemma unitClip_sq_lipschitz : LipschitzWith 2 (fun t => unitClip t ^ 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx := unitClip_mem x
  have hy := unitClip_mem y
  have hxy := unitClip_lipschitz.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hxy
  norm_num only [NNReal.coe_ofNat, Real.dist_eq]
  calc
    |unitClip x ^ 2 - unitClip y ^ 2| =
        |unitClip x - unitClip y| * |unitClip x + unitClip y| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |x - y| * 2 :=
      mul_le_mul hxy (by rw [abs_of_nonneg (add_nonneg hx.1 hy.1)]; linarith [hx.2, hy.2])
        (abs_nonneg _) (abs_nonneg _)
    _ = _ := by ring

/-- The squared clipping distance is at most the loss in the square.
[OD14, §11.7, clipping estimate] -/
lemma unitClip_sub_sq_le (t : ℝ) : (t - unitClip t) ^ 2 ≤ t ^ 2 - unitClip t ^ 2 := by
  rw [unitClip_eq]
  rcases le_total t 0 with ht | ht
  · rw [max_eq_left ht, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    ring_nf
    rfl
  · rw [max_eq_right ht]
    rcases le_total t 1 with ht1 | ht1
    · rw [min_eq_right ht1]
      simp
    · rw [min_eq_left ht1]
      nlinarith

/-- A loss of at most η in second moment bounds the L² clipping error by √η.
[OD14, §11.7, clipping step]

**Proof sketch.** Integrate the pointwise squared-distance bound. The second
moment of the difference is the square of its L² norm. -/
theorem unitClip_error_two_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → ℝ}
    (hU : MemLp U 2 μ) {η : ℝ}
    (hη : (∫ x, U x ^ 2 ∂μ) - (∫ x, unitClip (U x) ^ 2 ∂μ) ≤ η) :
    rvLpNorm (fun x => U x - unitClip (U x)) μ 2 ≤ Real.sqrt η := by
  have hR : MemLp (fun x => unitClip (U x)) 2 μ :=
    unitClip_lipschitz.comp_memLp (by norm_num [unitClip_eq]) hU
  have hD : MemLp (fun x => U x - unitClip (U x)) 2 μ := hU.sub hR
  have hsq : rvLpNorm (fun x => U x - unitClip (U x)) μ 2 ^ 2 =
      ∫ x, (U x - unitClip (U x)) ^ 2 ∂μ := by
    simpa only [Real.rpow_two, sq_abs] using
      rvLpNorm_rpow (fun x => U x - unitClip (U x)) μ 2 (by norm_num)
        (by simpa only [ENNReal.ofReal_ofNat] using hD)
  apply Real.le_sqrt_of_sq_le
  rw [hsq]
  calc
    _ ≤ ∫ x, U x ^ 2 - unitClip (U x) ^ 2 ∂μ :=
      integral_mono hD.integrable_sq (hU.integrable_sq.sub hR.integrable_sq)
        (fun x => unitClip_sub_sq_le (U x))
    _ = _ := integral_sub hU.integrable_sq hR.integrable_sq
    _ ≤ η := hη

/-- No-notables invariance controls the second moment lost by clipping the
Gaussian extension of the smoothed function. [OD14, §11.7, proof of (11.39)]

**Proof sketch.** A unit-interval-valued function has variance at most one.
Apply Lipschitz invariance to squared clipping, which is globally two-Lipschitz
and agrees with the square on the range of Boolean smoothing. -/
theorem clipped_second_moment_discrepancy :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 20 →
      (∀ i, KKL.noisyInfluence (1 - δ) i f ≤ ε) →
      |expect (fun x => noiseOp (1 - δ) f x ^ 2) -
        (∫ z : Fin n → ℝ, unitClip
          (evalMultilinearRV (fourierCoeff (noiseOp (1 - δ) f))
            (fun i z => z i) z) ^ 2
          ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))| ≤
        2 * K * ε ^ (δ / 3) := by
  obtain ⟨K, hK, hbound⟩ := invariance_no_notables
  refine ⟨K, hK, ?_⟩
  intro n f hf ε δ hε hε1 hδ hδ20 hinf
  have hmean : expect f ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact expect_nonneg (fun x => (hf x).1)
    · simpa using (expect_mono (g := fun _ => 1) (fun x => (hf x).2))
  have hvar : cubeVariance f ≤ 1 := by
    unfold cubeVariance
    calc
      _ ≤ expect (fun _ : BoolCube n => (1 : ℝ)) := expect_mono fun x => by
        have hx := hf x
        nlinarith [mul_nonneg
          (show 0 ≤ 1 - (f x - expect f) by linarith [hx.2, hmean.1])
          (show 0 ≤ 1 + (f x - expect f) by linarith [hx.1, hmean.2])]
      _ = 1 := by simp
  have hg (x : BoolCube n) : noiseOp (1 - δ) f x ∈ Set.Icc (0 : ℝ) 1 :=
    noiseOp_mem_unitInterval f hf ⟨by linarith, by linarith⟩ x
  have h := hbound f hvar ε δ hε hε1 hδ hδ20 hinf
    2 (fun t => unitClip t ^ 2) unitClip_sq_lipschitz
  simpa only [unitClip_eq_self (hg _), NNReal.coe_ofNat, mul_comm K 2] using h

/-- No-notables smoothing bounds the Gaussian clipping distance by
`√(2K) ε^(δ/6)` with a universal K. [OD14, §11.7, proof of (11.39)]

**Proof sketch.** Matching second moments converts the squared-clipping
invariance estimate to a loss of Gaussian second moment. Take square roots
using the preceding clipping-distance lemma. -/
theorem smoothed_clipping_error :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 20 →
      (∀ i, KKL.noisyInfluence (1 - δ) i f ≤ ε) →
      rvLpNorm (fun z : Fin n → ℝ =>
        evalMultilinearRV (fourierCoeff (noiseOp (1 - δ) f)) (fun i z => z i) z -
        unitClip (evalMultilinearRV (fourierCoeff (noiseOp (1 - δ) f))
          (fun i z => z i) z))
        (Measure.pi fun _ : Fin n => standardGaussianMeasure) 2 ≤
        Real.sqrt (2*K) * ε ^ (δ/6) := by
  obtain ⟨K, hK, hbound⟩ := clipped_second_moment_discrepancy
  refine ⟨K, hK, ?_⟩
  intro n f hf ε δ hε hε1 hδ hδ20 hinf
  letI : IsProbabilityMeasure standardGaussianMeasure :=
    hasInvarianceMoments_standardGaussian.reasonable.probability
  have hmoment := hbound f hf ε δ hε hε1 hδ hδ20 hinf
  have herror := unitClip_error_two_norm_le
    (gaussianExtension_memLp (noiseOp (1 - δ) f))
    (η := 2*K*ε^(δ/3)) (by
      rw [integral_gaussianExtension_sq]
      exact (le_abs_self _).trans hmoment)
  calc
    _ ≤ Real.sqrt (2*K*ε^(δ/3)) := herror
    _ = Real.sqrt (2*K) * ε ^ (δ/6) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2*K),
        Real.sqrt_eq_rpow (ε ^ (δ / 3)), ← Real.rpow_mul hε.le]
      congr 2
      ring

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- Clipping at L² distance at most d bounds stability by the Gaussian profile
at the original mean plus 4d. [OD14, §11.7, proof of (11.39)]

**Proof sketch.** Both inputs have L² norm at most one, so clipping changes
stability by at most 2d. Borell bounds the clipped stability. The mean changes
by at most d, and the diagonal Gaussian profile is two-Lipschitz. -/
theorem stability_le_profile_add_clipping_error {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    {U : (Fin n → ℝ) → ℝ} (hm : Measurable U)
    (hU : MemLp U 2 γ) (hUn : rvLpNorm U γ 2 ≤ 1)
    (hmean : (∫ x, U x ∂γ) ∈ Set.Icc (0 : ℝ) 1)
    {d : ℝ} (hd : rvLpNorm (fun x => U x - unitClip (U x)) γ 2 ≤ d) :
    gaussianNoiseStability ρ U ≤ gaussianHalfspaceStability ρ
      (∫ x, U x ∂γ) + 4 * d := by
  letI : IsProbabilityMeasure standardGaussianMeasure :=
    hasInvarianceMoments_standardGaussian.reasonable.probability
  let R : (Fin n → ℝ) → ℝ := fun x => unitClip (U x)
  have hR : MemLp R 2 γ :=
    unitClip_lipschitz.comp_memLp (by norm_num [unitClip_eq]) hU
  have hRm : Measurable R := unitClip_lipschitz.continuous.measurable.comp hm
  have hRrange (x : Fin n → ℝ) : R x ∈ Set.Icc (0 : ℝ) 1 := unitClip_mem _
  have hRi := hR.integrable (by norm_num)
  have hRn : rvLpNorm R γ 2 ≤ 1 := by
    have hs : rvLpNorm R γ 2 ^ 2 = ∫ x, R x ^ 2 ∂γ := by
      simpa only [Real.rpow_two, sq_abs] using
        rvLpNorm_rpow R γ 2 (by norm_num)
          (by simpa only [ENNReal.ofReal_ofNat] using hR)
    have hi : (∫ x, R x ^ 2 ∂γ) ≤ 1 := by
      calc
        _ ≤ ∫ _ : Fin n → ℝ, (1 : ℝ) ∂γ :=
          integral_mono hR.integrable_sq (integrable_const 1) fun x => by
            have hx := hRrange x
            nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
        _ = 1 := by simp
    have hn : 0 ≤ rvLpNorm R γ 2 := ENNReal.toReal_nonneg
    nlinarith
  have hRmean : (∫ x, R x ∂γ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact integral_nonneg (fun x => (hRrange x).1)
    · calc
        _ ≤ ∫ _ : Fin n → ℝ, (1 : ℝ) ∂γ :=
          integral_mono hRi (integrable_const 1) (fun x => (hRrange x).2)
        _ = 1 := by simp
  have hc : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  have hstab := gaussianNoiseStability_sub_le hc hU hR hUn hRn
  have hb := borell ρ hρ R hRm hRrange
  have hmeans : |(∫ x, U x ∂γ) - ∫ x, R x ∂γ| ≤ d := by
    have h := Invariance.lipschitz_integral_sub_le_two_norm hU hR
      (show LipschitzWith 1 (id : ℝ → ℝ) from LipschitzWith.id)
    have hn : |(∫ x, U x ∂γ) - ∫ x, R x ∂γ| ≤
        rvLpNorm (fun x => U x - R x) γ 2 := by
      simpa only [id_eq, NNReal.coe_one, one_mul] using h
    exact hn.trans hd
  have hp := abs_gaussianBivariateStability_sub_le hc hmean hmean hRmean hRmean
  simp only [gaussianBivariateStability_diag] at hp
  have hd' : rvLpNorm (fun x => U x - R x) γ 2 ≤ d := hd
  have hs := (le_abs_self _).trans hstab
  have hprof := (neg_le_abs _).trans hp
  linarith

end BooleanAnalysis.GaussianSpace.MajorityIsStablest
