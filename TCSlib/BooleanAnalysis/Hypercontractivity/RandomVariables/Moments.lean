/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.Polynomial
import Mathlib.Probability.Independence.Integration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Moments of multilinear polynomials on standardized independent inputs

## Main definitions

The existing multilinear coefficient representation and random-input evaluation are reused.

## Main results

* `MultilinearMoments.integral_monomial_mul`: orthonormality of multilinear monomials.
* `MultilinearMoments.monomial_memLp`: finite fourth moments of each monomial.
* `MultilinearMoments.integral_eval_mul`: the coefficient inner product identity.
* `MultilinearMoments.integral_eval_sq`: the coefficient second-moment identity.
* `MultilinearMoments.integral_eval`: the mean is the constant coefficient.
* `MultilinearMoments.eval_supported`: evaluation restricted to an active coordinate set.
* `MultilinearMoments.eval_eq_of_off_coordinate`: changing an unused input preserves evaluation.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Definition 11.63 and Hypothesis 11.65.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity

/-- Distinct multilinear monomials in independent centered unit-second-moment
inputs are orthogonal, and every monomial has second moment one.
[OD14, §11.6, Def. 11.63 and Remark 11.64]
Only second moments are needed, so the assumptions are weaker than Hypothesis 11.65.

**Proof sketch.** Extend both finite products by one outside their index sets.
Independence factors the integral into coordinate moments. A coordinate appearing
twice contributes its second moment, a coordinate appearing once contributes its
mean, and an absent coordinate contributes one. Equal index sets therefore give
one; unequal sets contain a coordinate contributing zero. -/
theorem MultilinearMoments.integral_monomial_mul
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1)
    (S T : Finset ι) :
    (∫ ω, (∏ i ∈ S, X i ω) * (∏ i ∈ T, X i ω) ∂μ) =
      if S = T then 1 else 0 := by
  classical
  let f : ι → ℝ → ℝ := fun i x =>
    (if i ∈ S then x else 1) * (if i ∈ T then x else 1)
  calc
    _ = ∫ ω, ∏ i, f i (X i ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [f, Finset.prod_mul_distrib, Fintype.prod_ite_mem]
    _ = ∏ i, ∫ ω, f i (X i ω) ∂μ :=
      hI.integral_fun_prod_comp
        (fun i => (hX i).aestronglyMeasurable.aemeasurable)
        (fun i => by dsimp [f]; split_ifs <;> fun_prop)
    _ = _ := by
      split_ifs with hST
      · subst T
        apply Finset.prod_eq_one
        intro i hi
        by_cases hiS : i ∈ S
        · simpa [f, hiS, ← pow_two] using hsecond i
        · simp [f, hiS]
      · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
          by_contra h
          apply hST
          ext i
          exact Classical.byContradiction fun hi => h ⟨i, hi⟩
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
          simp_all [f]

/-- A multilinear monomial in independent inputs with finite fourth moments
has a finite fourth moment. This specializes polynomial integrability from
[OD14, Cor. 9.6 (proof)].

**Proof sketch.** Represent the monomial by the multilinear coefficient
function supported at its index set, then apply fourth-moment integrability
of multilinear polynomial evaluations. -/
theorem MultilinearMoments.monomial_memLp
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ) (S : Finset (Fin n)) :
    MemLp (fun ω => ∏ i ∈ S, X i ω) 4 μ := by
  classical
  have h := evalMultilinearRV_memLp (fun T => if T = S then 1 else 0) X μ hI hX
  change MemLp (fun ω =>
    ∑ T : Finset (Fin n), (if T = S then 1 else 0) * ∏ i ∈ T, X i ω) 4 μ at h
  simpa using h

/-- The expected product of two multilinear polynomial evaluations in independent
centered unit-second-moment inputs equals the inner product of their coefficient
vectors. [OD14, §11.6, Remark 11.64]
Finite fourth moments are assumed to reuse the existing polynomial integrability
infrastructure; finite second moments would suffice mathematically.

**Proof sketch.** Expand the product into a finite double sum. The monomial
fourth-moment bounds make each product integrable, so the sums may pass through
the integral. Monomial orthogonality eliminates all terms off the diagonal. -/
theorem MultilinearMoments.integral_eval_mul
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F G : ThresholdFunctions.MultilinearPolynomial n)
    (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1) :
    (∫ ω, evalMultilinearRV F X ω * evalMultilinearRV G X ω ∂μ) =
      ∑ S : Finset (Fin n), F S * G S := by
  classical
  have hm (S : Finset (Fin n)) :
      MemLp (fun ω => ∏ i ∈ S, X i ω) 2 μ :=
    (MultilinearMoments.monomial_memLp X hI hX S).mono_exponent (by norm_num)
  have hint (S T : Finset (Fin n)) :
      Integrable (fun ω => (F S * G T) *
        ((∏ i ∈ S, X i ω) * (∏ i ∈ T, X i ω))) μ :=
    ((hm S).integrable_mul (hm T)).const_mul (F S * G T)
  calc
    _ = ∫ ω, ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        (F S * G T) * ((∏ i ∈ S, X i ω) * (∏ i ∈ T, X i ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [evalMultilinearRV, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      ring
    _ = ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        ∫ ω, (F S * G T) * ((∏ i ∈ S, X i ω) * (∏ i ∈ T, X i ω)) ∂μ := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro S hS
        exact integral_finset_sum _ (fun T hT => hint S T)
      · intro S hS
        exact integrable_finset_sum _ (fun T hT => hint S T)
    _ = _ := by
      simp_rw [integral_const_mul, MultilinearMoments.integral_monomial_mul X hI
        (fun i => (hX i).mono_exponent (by norm_num)) hmean hsecond]
      simp

/-- The second moment of a multilinear polynomial on independent centered
unit-second-moment inputs is the sum of its squared coefficients.
[OD14, §11.6, Remark 11.64]
Finite fourth moments are retained from the inner product identity. -/
theorem MultilinearMoments.integral_eval_sq
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : ThresholdFunctions.MultilinearPolynomial n)
    (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1) :
    (∫ ω, evalMultilinearRV F X ω ^ 2 ∂μ) =
      ∑ S : Finset (Fin n), F S ^ 2 := by
  simpa only [pow_two] using
    MultilinearMoments.integral_eval_mul F F X hI hX hmean hsecond

/-- The mean of a multilinear polynomial on independent centered
unit-second-moment inputs is its constant coefficient.
[OD14, §11.6, Remark 11.64]
The moment assumptions are retained from the inner product identity. -/
theorem MultilinearMoments.integral_eval
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : ThresholdFunctions.MultilinearPolynomial n)
    (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) 4 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) = 1) :
    (∫ ω, evalMultilinearRV F X ω ∂μ) = F ∅ := by
  classical
  have hc : evalMultilinearRV (fun S => if S = ∅ then 1 else 0) X =
      fun _ => (1 : ℝ) := by
    funext ω
    simp [evalMultilinearRV]
  simpa [hc] using
    MultilinearMoments.integral_eval_mul F
      (fun S => if S = ∅ then 1 else 0) X hI hX hmean hsecond

/-- If every nonzero coefficient is indexed by a subset of `s`, polynomial
evaluation is the sum over the subsets of `s`. -/
theorem MultilinearMoments.eval_supported
    {n : ℕ} {Ω : Type*}
    (F : ThresholdFunctions.MultilinearPolynomial n) (X : Fin n → Ω → ℝ)
    (s : Finset (Fin n)) (hF : ∀ T, ¬ T ⊆ s → F T = 0) (ω : Ω) :
    evalMultilinearRV F X ω = ∑ T ∈ s.powerset, F T * ∏ j ∈ T, X j ω := by
  classical
  unfold evalMultilinearRV
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro T hT hs
  rw [hF T (by simpa only [Finset.mem_powerset] using hs), zero_mul]

/-- If no nonzero monomial uses coordinate `i`, evaluation is unchanged when
only that coordinate's input changes. -/
theorem MultilinearMoments.eval_eq_of_off_coordinate
    {n : ℕ} {Ω : Type*}
    (F : ThresholdFunctions.MultilinearPolynomial n) (i : Fin n)
    (X Y : Fin n → Ω → ℝ)
    (hF : ∀ S, i ∈ S → F S = 0) (hXY : ∀ j, j ≠ i → X j = Y j) :
    evalMultilinearRV F X = evalMultilinearRV F Y := by
  classical
  funext ω
  unfold evalMultilinearRV
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hiS : i ∈ S
  · simp [hF S hiS]
  · congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact congrFun (hXY j (by rintro rfl; exact hiS hj)) ω

end BooleanAnalysis.Hypercontractivity
