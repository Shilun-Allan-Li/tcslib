/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance
import TCSlib.BooleanAnalysis.GaussianSpace.InputMoments
import TCSlib.BooleanAnalysis.GaussianSpace.Halfspace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Normalized independent sums and Gaussian approximation

## Main definitions

* `normalizedSumPolynomial`: the existing multilinear-polynomial representation
  of the sum of coordinates divided by the square root of their number.

## Main results

* The normalized-sum polynomial has degree at most one, coordinate influences
  one divided by the dimension, and variance one in positive dimension.
* A normalized sum of independent inputs satisfying the invariance moment
  hypotheses approximates a standard Gaussian for every Lipschitz test, with
  error at most a universal constant times the test constant times n^(-1/4).

This supplies the scalar normalized-bit bridge for Gaussian Bobkov. It derives
from the already proved fourth-order invariance principle, rather than the
uncompleted Berry–Esseen statement elsewhere in the library. The estimate is
stated for arbitrary independent moment-matched inputs, which need not have
the same distribution.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, BitsToGaussians, and §11.6, Corollary 11.68.
-/

open MeasureTheory Filter
open scoped BigOperators NNReal ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

/-- The normalized-sum polynomial has coefficient one over the square root of
the dimension on each singleton and zero on all other monomials.
[OD14, §11.1, BitsToGaussians]
It uses the existing multilinear-polynomial type and is total in dimension zero. -/
noncomputable def normalizedSumPolynomial (n : ℕ) : MultilinearPolynomial n :=
  fun S => if S.card = 1 then 1 / Real.sqrt n else 0

/-- The normalized-sum polynomial has degree at most one.
[OD14, §11.1, BitsToGaussians] -/
lemma normalizedSumPolynomial_hasDegreeAtMost (n : ℕ) :
    (normalizedSumPolynomial n).HasDegreeAtMost 1 := by
  intro S hS
  simp [normalizedSumPolynomial, ne_of_gt hS]

/-- Every coordinate influence of the normalized-sum polynomial is one divided
by the dimension. [OD14, §11.1, BitsToGaussians]

**Proof sketch.** In the coefficient formula for influence, the only nonzero
monomial containing the chosen coordinate is its singleton. Square its coefficient. -/
lemma influence_normalizedSumPolynomial (n : ℕ) (i : Fin n) :
    influence i (normalizedSumPolynomial n).eval = 1 / (n : ℝ) := by
  classical
  rw [influence_eq_sum_fourier]
  simp only [MultilinearPolynomial.fourierCoeff_eval]
  rw [Finset.sum_eq_single {i}]
  · simp [normalizedSumPolynomial, Real.sq_sqrt (Nat.cast_nonneg n)]
  · intro S _ hSi
    by_cases himem : i ∈ S
    · by_cases hcard : S.card = 1
      · rcases Finset.card_eq_one.mp hcard with ⟨j, rfl⟩
        have hij : i = j := by simpa only [Finset.mem_singleton] using himem
        subst j
        exact (hSi rfl).elim
      · simp [normalizedSumPolynomial, himem, hcard]
    · simp [himem]
  · simp

/-- In positive dimension the normalized-sum polynomial has variance one.
[OD14, §11.1, BitsToGaussians]

**Proof sketch.** All nonzero coefficients have degree one, so variance equals
total influence. Sum the coordinate influences, each one divided by the dimension. -/
lemma cubeVariance_normalizedSumPolynomial (n : ℕ) (hn : 0 < n) :
    cubeVariance (normalizedSumPolynomial n).eval = 1 := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    cubeVariance (normalizedSumPolynomial n).eval =
        totalInfluence (normalizedSumPolynomial n).eval := by
      rw [cubeVariance_eq_sum_nonempty_fourier, totalInfluence_eq_sum_sq_deg]
      simp only [MultilinearPolynomial.fourierCoeff_eval]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : S.card = 1
      · have hne : S ≠ ∅ := by
          intro hS
          subst S
          simp at hcard
        simp [normalizedSumPolynomial, hcard, hne]
      · simp [normalizedSumPolynomial, hcard]
    _ = 1 := by simp [totalInfluence, influence_normalizedSumPolynomial, hn']

/-- Evaluating the normalized-sum polynomial at arbitrary random inputs gives
the sum of the inputs divided by the square root of the dimension.
[OD14, §11.1, BitsToGaussians]

**Proof sketch.** Restrict the coefficient sum to singleton monomials, identify
these with coordinates, and factor out the common normalization. -/
lemma evalMultilinearRV_normalizedSumPolynomial {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (X : Fin n → Ω → ℝ) (ω : Ω) :
    evalMultilinearRV (normalizedSumPolynomial n) X ω =
      (∑ i : Fin n, X i ω) / Real.sqrt n := by
  classical
  let T := Finset.univ.image (fun i : Fin n => ({i} : Finset (Fin n)))
  have hzero : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))), S ∉ T →
      normalizedSumPolynomial n S * ∏ i ∈ S, X i ω = 0 := by
    intro S _ hS
    by_cases hcard : S.card = 1
    · rcases Finset.card_eq_one.mp hcard with ⟨i, rfl⟩
      exact (hS (by simp [T])).elim
    · simp [normalizedSumPolynomial, hcard]
  unfold evalMultilinearRV
  rw [← Finset.sum_subset (Finset.subset_univ T) hzero]
  dsimp [T]
  rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  simp only [normalizedSumPolynomial, Finset.card_singleton, ite_true,
    Finset.prod_singleton, one_div]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- Normalized sums of independent inputs satisfying the invariance moment
hypotheses approximate a standard Gaussian for Lipschitz tests, with a universal
error constant times n^(-1/4). [OD14, Cor. 11.68, degree-one specialization]
The input laws may differ; no identical-distribution assumption is imposed.

**Proof sketch.** Apply Lipschitz invariance to the degree-one normalized-sum
polynomial, with variance one and maximum influence one divided by n. Compare
to independent standard Gaussian coordinates, which satisfy the same moment
hypotheses. Their normalized sum has the standard Gaussian law by the unit
projection theorem. The degree-one factor two is absorbed into the universal
constant. Finite fourth moments ensure the tested inputs are integrable. -/
lemma normalizedSum_lipschitz_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : ℕ}, 0 < n →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin n → Ω → ℝ), ProbabilityTheory.iIndepFun X μ →
        (∀ i, HasInvarianceMoments (X i) μ) →
        ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ →
          |(∫ ω, ψ ((∑ i : Fin n, X i ω) / Real.sqrt n) ∂μ) -
            ∫ y : ℝ, ψ y ∂standardGaussianMeasure| ≤
            K * (c : ℝ) * (1 / (n : ℝ)) ^ (1 / 4 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := invariance_lipschitz
  refine ⟨2 * K, by positivity, ?_⟩
  intro n hn Ω _ μ _ X hIX hX c ψ hψ
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hY (i : Fin n) : HasInvarianceMoments (fun z : Fin n → ℝ => z i) ν :=
    hasInvarianceMoments_gaussianCoordinate i
  have ha : (∑ _i : Fin n, (1 / Real.sqrt n) ^ 2) = 1 := by
    simp [Real.sq_sqrt (Nat.cast_nonneg n), hn']
  have hlaw : ν.map (fun z : Fin n → ℝ => (∑ i, z i) / Real.sqrt n) =
      standardGaussianMeasure := by
    simpa only [one_div_mul_eq_div, ← Finset.sum_div] using
      (measurePreserving_gaussianProjection (fun _ : Fin n => 1 / Real.sqrt n) ha).map_eq
  have eY : (∫ z : Fin n → ℝ, ψ ((∑ i, z i) / Real.sqrt n) ∂ν) =
      ∫ y : ℝ, ψ y ∂standardGaussianMeasure := by
    have h := integral_map (μ := ν)
      (φ := fun z : Fin n → ℝ => (∑ i, z i) / Real.sqrt n) (f := ψ)
      (by fun_prop) hψ.continuous.aestronglyMeasurable
    rw [hlaw] at h
    exact h.symm
  have h := hbound μ ν (normalizedSumPolynomial n)
    (normalizedSumPolynomial_hasDegreeAtMost n)
    (by rw [cubeVariance_normalizedSumPolynomial n hn])
    (1 / (n : ℝ)) (by positivity)
    (fun i => (influence_normalizedSumPolynomial n i).le)
    X (fun (i : Fin n) (z : Fin n → ℝ) => z i) hIX
    (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => standardGaussianMeasure)
      (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable))
    hX hY c ψ hψ
  simp only [evalMultilinearRV_normalizedSumPolynomial, eY] at h
  convert h using 1
  ring

/-- Normalized sums of independent uniform Boolean signs approximate a standard
Gaussian for Lipschitz tests, with a universal error constant times n^(-1/4).
[OD14, §11.1, BitsToGaussians; Cor. 11.68]

**Proof sketch.** Uniform Boolean signs have the required four moments. Transfer
these moment hypotheses to coordinate evaluations under the product law and
apply the general normalized-sum comparison. -/
lemma normalizedBoolSum_lipschitz_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 0 < n →
      ∀ (c : ℝ≥0) (ψ : ℝ → ℝ), LipschitzWith c ψ →
        |(∫ x : Fin n → Bool, ψ ((∑ i, boolToSign (x i)) / Real.sqrt n)
            ∂(Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)) -
          ∫ y : ℝ, ψ y ∂standardGaussianMeasure| ≤
          K * (c : ℝ) * (1 / (n : ℝ)) ^ (1 / 4 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := normalizedSum_lipschitz_comparison
  refine ⟨K, hK, ?_⟩
  intro n hn c ψ hψ
  let μ : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
  have hX (i : Fin n) : HasInvarianceMoments
      (fun x : Fin n → Bool => boolToSign (x i)) (Measure.pi fun _ : Fin n => μ) := by
    exact hasInvarianceMoments_uniformBoolCoordinate i
  exact hbound hn (Measure.pi fun _ : Fin n => μ)
    (fun (i : Fin n) (x : Fin n → Bool) => boolToSign (x i))
    (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => μ) (X := fun _ : Fin n => boolToSign)
      (fun _ => (measurable_of_finite boolToSign).aemeasurable)) hX c ψ hψ

/-- Normalized sums of increasing numbers of independent uniform Boolean signs
converge to a standard Gaussian when tested by a Lipschitz function.
[OD14, §11.1, BitsToGaussians]
The dimension is written m+1 to keep every normalization positive.

**Proof sketch.** The quantitative comparison bounds the absolute expectation
difference by a constant times (m+1)^(-1/4), which tends to zero. Squeeze the
absolute difference to obtain convergence of expectations. -/
lemma tendsto_integral_normalizedBoolSum (c : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : LipschitzWith c ψ) :
    Tendsto (fun m : ℕ =>
      ∫ x : Fin (m + 1) → Bool,
        ψ ((∑ i, boolToSign (x i)) / Real.sqrt (m + 1))
        ∂(Measure.pi fun _ : Fin (m + 1) => (PMF.uniformOfFintype Bool).toMeasure))
      atTop (𝓝 (∫ y : ℝ, ψ y ∂standardGaussianMeasure)) := by
  obtain ⟨K, -, hbound⟩ := normalizedBoolSum_lipschitz_comparison
  have hi : Tendsto (fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsmall : Tendsto (fun m : ℕ =>
      K * (c : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    have h := (hi.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))).const_mul
      (K * (c : ℝ))
    simpa using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hsmall
  simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using
    hbound (m + 1) (Nat.succ_pos m) c ψ hψ

/-- Cube expectations of Lipschitz tests of normalized Boolean sums converge
to the standard Gaussian expectation. [OD14, §11.1, BitsToGaussians]

**Proof sketch.** Identify cube expectation with integration under independent
uniform Boolean coordinates, then apply the normalized-sum limit. -/
lemma tendsto_expect_normalizedBoolSum (c : ℝ≥0) (ψ : ℝ → ℝ)
    (hψ : LipschitzWith c ψ) :
    Tendsto (fun m : ℕ => expect (fun x : BoolCube (m + 1) =>
      ψ ((∑ i, boolToSign (x i)) / Real.sqrt (m + 1))))
      atTop (𝓝 (∫ y : ℝ, ψ y ∂standardGaussianMeasure)) := by
  simpa only [integral_uniformBool_pi_eq_expect] using
    tendsto_integral_normalizedBoolSum c ψ hψ

end BooleanAnalysis.GaussianSpace
