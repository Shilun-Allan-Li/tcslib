/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance
import Mathlib.Analysis.Complex.ExponentialBounds
import TCSlib.BooleanAnalysis.GaussianSpace.InputMoments
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Perturbation
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Low-degree truncation for invariance

## Main definitions

The existing Fourier truncations and polynomial evaluations are reused.

## Main results

* `invariance_lipschitz_boolean_gaussian`: the Boolean-to-Gaussian specialization.
* `lowDegreePart_polynomial_degree`, `lowDegreePart_variance_le`: truncation bounds.
* `invariance_cutoff_nonneg`, `invariance_cutoff_exp`, `invariance_cutoff_power_le`:
  logarithmic cutoff estimates.
* `highDegree_noise_l2Norm_le_exp`: exponential L² decay of the smoothed tail.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Corollaries 11.68–11.69.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanAnalysis.GaussianSpace.Invariance

open ThresholdFunctions Hypercontractivity

/-- A degree-bounded Boolean function with small influences satisfies Lipschitz
invariance against its Gaussian polynomial extension. [OD14, Cor. 11.68]

**Proof sketch.** Use independent uniform Boolean signs and Gaussian coordinates
in the general Lipschitz invariance theorem. Fourier inversion identifies the
Boolean evaluation and the uniform product integral is cube expectation. -/
theorem invariance_lipschitz_boolean_gaussian :
    ∃ K : ℝ, 0 < K ∧ ∀ {n d : ℕ} (f : BooleanFunc n),
      MultilinearPolynomial.HasDegreeAtMost (fourierCoeff f) d →
      cubeVariance f ≤ 1 → ∀ ε : ℝ, 0 ≤ ε →
      (∀ i, influence i f ≤ ε) → ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ →
      |expect (fun x => ψ (f x)) - ∫ z : Fin n → ℝ,
        ψ (evalMultilinearRV (fourierCoeff f) (fun i z => z i) z)
          ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)| ≤
        K * (c : ℝ) * (2 : ℝ) ^ d * ε ^ (1 / 4 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := invariance_lipschitz
  refine ⟨K, hK, ?_⟩
  intro n d f hdegree hvar ε hε hinf c ψ hψ
  letI : IsProbabilityMeasure standardGaussianMeasure :=
    hasInvarianceMoments_standardGaussian.reasonable.probability
  let μ : Measure (BoolCube n) :=
    Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  have hX (i : Fin n) :
      HasInvarianceMoments (fun x : BoolCube n => boolToSign (x i)) μ :=
    hasInvarianceMoments_uniformBoolCoordinate i
  have hY (i : Fin n) :
      HasInvarianceMoments (fun z : Fin n → ℝ => z i) ν :=
    hasInvarianceMoments_gaussianCoordinate i
  have hIX : iIndepFun (fun (i : Fin n) (x : BoolCube n) => boolToSign (x i)) μ :=
    iIndepFun_pi (μ := fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)
      (X := fun _ => boolToSign) (fun _ => (measurable_of_finite boolToSign).aemeasurable)
  have hIY : iIndepFun (fun (i : Fin n) (z : Fin n → ℝ) => z i) ν :=
    iIndepFun_pi (μ := fun _ : Fin n => standardGaussianMeasure)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have heval : evalMultilinearRV (fourierCoeff f)
      (fun (i : Fin n) (x : BoolCube n) => boolToSign (x i)) = f := by
    funext x
    simpa only [evalMultilinearRV, chiS] using (walsh_expansion f x).symm
  have h := hbound μ ν (fourierCoeff f) hdegree
    (by simpa only [MultilinearPolynomial.eval_fourierCoeff] using hvar)
    ε hε (by simpa only [MultilinearPolynomial.eval_fourierCoeff] using hinf)
    (fun (i : Fin n) (x : BoolCube n) => boolToSign (x i))
    (fun (i : Fin n) (z : Fin n → ℝ) => z i) hIX hIY hX hY c ψ hψ
  simpa only [heval, μ, ν, integral_uniformBool_pi_eq_expect] using h

/-- The Fourier coefficient polynomial of the low-degree part has degree at most
the truncation cutoff. [OD14, §3.1] -/
lemma lowDegreePart_polynomial_degree {n : ℕ} (f : BooleanFunc n) (d : ℕ) :
    MultilinearPolynomial.HasDegreeAtMost (fourierCoeff (KKL.lowDegreePart f d)) d := by
  intro S hS
  rw [KKL.fourierCoeff_lowDegreePart, if_neg (Nat.not_le.mpr hS)]

/-- Removing Fourier levels above a cutoff cannot increase variance.
[OD14, §3.1, orthogonality of Fourier levels] -/
lemma lowDegreePart_variance_le {n : ℕ} (f : BooleanFunc n) (d : ℕ) :
    cubeVariance (KKL.lowDegreePart f d) ≤ cubeVariance f := by
  classical
  rw [cubeVariance_eq_sum_nonempty_fourier, cubeVariance_eq_sum_nonempty_fourier]
  apply Finset.sum_le_sum
  intro S hS
  by_cases hE : S = ∅
  · simp [hE]
  · simp only [if_neg hE, KKL.fourierCoeff_lowDegreePart]
    split_ifs <;> simp [sq_nonneg]

/-- The logarithmic truncation cutoff is nonnegative for an influence parameter
in `(0,1]`. [OD14, Cor. 11.69 (proof)] -/
lemma invariance_cutoff_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ Real.log (1 / ε) / 3 := by
  have hinv : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
  exact div_nonneg (Real.log_nonneg hinv) (by norm_num)

/-- Exponential Fourier decay at the logarithmic cutoff is the target influence
power. [OD14, Cor. 11.69 (proof)] -/
lemma invariance_cutoff_exp {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    Real.exp (-δ * (Real.log (1 / ε) / 3)) = ε ^ (δ / 3) := by
  rw [Real.rpow_def_of_pos hε, one_div, Real.log_inv]
  congr 1
  ring

/-- The low-degree error at the logarithmic cutoff is at most the target noise
power when `δ ≤ 1/20`. [OD14, Cor. 11.69 (proof)] -/
lemma invariance_cutoff_power_le {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ ≤ 1 / 20) :
    (2 : ℝ) ^ (Real.log (1 / ε) / 3) * ε ^ (1 / 4 : ℝ) ≤ ε ^ (δ / 3) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hε, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [one_div, Real.log_inv]
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hlog2 : Real.log 2 ≤ 7 / 10 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hcoef : δ / 3 ≤ 1 / 4 - Real.log 2 / 3 := by linarith
  nlinarith [mul_le_mul_of_nonpos_left hcoef hlogε]

/-- The high-degree tail after noise smoothing is at most `exp(-δ k)` in L²
when the original variance is at most one. [OD14, Cor. 11.69 (proof)]

**Proof sketch.** Parseval expresses the tail as squared coefficients. Each
retained level exceeds the real cutoff and its noise multiplier is at most
`exp(-δ k)`. The remaining coefficient energy is bounded by variance. -/
theorem highDegree_noise_l2Norm_le_exp {n : ℕ} (f : BooleanFunc n)
    (hvar : cubeVariance f ≤ 1) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (k : ℝ) (hk : 0 ≤ k) :
    l2Norm (KKL.highDegreePart (noiseOp (1 - δ) f) ⌊k⌋₊) ≤ Real.exp (-δ * k) := by
  classical
  have hρ : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  have hpower (m : ℕ) (hm : k ≤ (m : ℝ)) :
      (1 - δ) ^ m ≤ Real.exp (-δ * k) := by
    calc
      _ ≤ Real.exp (-δ) ^ m :=
        pow_le_pow_left₀ hρ (Real.one_sub_le_exp_neg δ) m
      _ = Real.exp (-δ * (m : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (-δ * k) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr hδ0))
  have hsq : innerProduct
      (KKL.highDegreePart (noiseOp (1 - δ) f) ⌊k⌋₊)
      (KKL.highDegreePart (noiseOp (1 - δ) f) ⌊k⌋₊) ≤
        Real.exp (-δ * k) ^ 2 := by
    calc
      _ = ∑ S : Finset (Fin n), if ⌊k⌋₊ < S.card then
          ((1 - δ) ^ S.card * fourierCoeff f S) ^ 2 else 0 := by
        rw [parseval]
        apply Finset.sum_congr rfl
        intro S hS
        rw [KKL.fourierCoeff_highDegreePart]
        by_cases ht : ⌊k⌋₊ < S.card <;> simp [ht, noiseOp_fourier]
      _ ≤ Real.exp (-δ * k) ^ 2 * cubeVariance f := by
        rw [cubeVariance_eq_sum_nonempty_fourier, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro S hS
        by_cases ht : ⌊k⌋₊ < S.card
        · have hne : S ≠ ∅ := by
            intro he
            subst S
            simp at ht
          simp only [if_pos ht, if_neg hne, mul_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (pow_nonneg hρ _)
              (hpower S.card ((Nat.floor_lt hk).mp ht).le) 2) (sq_nonneg _)
        · simp only [if_neg ht]
          split_ifs <;> positivity
      _ ≤ Real.exp (-δ * k) ^ 2 :=
        mul_le_of_le_one_right (sq_nonneg _) hvar
  unfold l2Norm
  calc
    _ ≤ Real.sqrt (Real.exp (-δ * k) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = _ := Real.sqrt_sq (Real.exp_nonneg _)

end BooleanAnalysis.GaussianSpace.Invariance
