/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Moments
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Polynomial
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.LinearThresholdInfluence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coordinate decomposition of multilinear polynomials

## Main definitions

* `Invariance.coordinateFree`: the terms omitting a specified coordinate.
* `Invariance.coordinateDerivative`: the coefficients of the existing cube derivative.

## Main results

* `Invariance.coordinateDerivative_coeff`: the coefficient formula for the derivative.
* `Invariance.coordinateDerivative_degree`: a coordinate derivative lowers the degree.
* `Invariance.coordinateDerivative_eval`: the adapter evaluates to the existing cube derivative.
* `Invariance.coordinateDerivative_sum_sq`: the derivative's squared coefficients sum to influence.
* `Invariance.coordinateFree_eval_sum`: the coordinate-free evaluation over the remaining inputs.
* `Invariance.coordinateDerivative_eval_sum`: the derivative evaluation over the remaining inputs.
* `Invariance.eval_coordinate_split`: the coordinate-free part plus the input times its derivative.
* `Invariance.indep_coordinate_parts`: independence from the joint coordinate-free background.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §2.2 and §11.6, proof of (11.29).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace.Invariance

open ThresholdFunctions Hypercontractivity

/-- The part of a multilinear polynomial whose monomials omit coordinate `i`.
[OD14, §11.6, proof of (11.29), coordinate decomposition] -/
def coordinateFree {n : ℕ}
    (F : MultilinearPolynomial n) (i : Fin n) : MultilinearPolynomial n :=
  fun S => if i ∈ S then 0 else F S

/-- The coefficient vector of the existing Boolean derivative of `F.eval`.
It evaluates the same multilinear derivative on arbitrary real inputs.
[OD14, §2.2; §11.6, proof of (11.29)] -/
noncomputable def coordinateDerivative {n : ℕ}
    (F : MultilinearPolynomial n) (i : Fin n) : MultilinearPolynomial n :=
  fun S => fourierCoeff (BooleanAnalysis.derivative i F.eval) S

/-- A coordinate derivative removes that coordinate from each monomial containing it,
and has zero coefficients on sets still containing the coordinate.
[OD14, §2.2, Fourier expansion of discrete derivatives] -/
lemma coordinateDerivative_coeff {n : ℕ}
    (F : MultilinearPolynomial n) (i : Fin n) (S : Finset (Fin n)) :
    coordinateDerivative F i S = if i ∈ S then 0 else F (insert i S) := by
  simp only [coordinateDerivative, fourierCoeff_derivative, F.fourierCoeff_eval]

/-- The coordinate derivative of a polynomial of degree at most `k + 1`
has degree at most `k`. [OD14, §11.6, proof of (11.29)] -/
lemma coordinateDerivative_degree {n k : ℕ}
    (F : MultilinearPolynomial n) (i : Fin n) (hF : F.HasDegreeAtMost (k + 1)) :
    (coordinateDerivative F i).HasDegreeAtMost k := by
  classical
  intro S hS
  rw [coordinateDerivative_coeff]
  split_ifs with hi
  · rfl
  · apply hF
    rw [Finset.card_insert_of_notMem hi]
    omega

/-- Evaluating the derivative coefficient vector on the cube recovers the
existing Boolean derivative. [OD14, §1.4, Fourier inversion; §2.2] -/
lemma coordinateDerivative_eval {n : ℕ}
    (F : MultilinearPolynomial n) (i : Fin n) :
    (coordinateDerivative F i).eval = BooleanAnalysis.derivative i F.eval := by
  funext x
  exact (walsh_expansion (BooleanAnalysis.derivative i F.eval) x).symm

/-- The squared coefficients of a coordinate derivative sum to that coordinate's
influence on the original cube polynomial. [OD14, §2.2; §11.6, Def. 11.63] -/
lemma coordinateDerivative_sum_sq {n : ℕ}
    (F : MultilinearPolynomial n) (i : Fin n) :
    (∑ S : Finset (Fin n), coordinateDerivative F i S ^ 2) = influence i F.eval := by
  rw [← (coordinateDerivative F i).expect_eval_sq,
    coordinateDerivative_eval, ← influence_eq_expect_derivative_sq]

/-- Evaluating the coordinate-free part sums exactly the monomials on the
remaining coordinates. [OD14, §11.6, proof of (11.29)] -/
lemma coordinateFree_eval_sum {n : ℕ} {Ω : Type*}
    (F : MultilinearPolynomial n) (i : Fin n) (X : Fin n → Ω → ℝ) (ω : Ω) :
    evalMultilinearRV (coordinateFree F i) X ω =
      ∑ T ∈ (Finset.univ.erase i).powerset, F T * ∏ j ∈ T, X j ω := by
  classical
  rw [MultilinearMoments.eval_supported (coordinateFree F i) X (Finset.univ.erase i)
    (fun T hT => by
      have hi : i ∈ T := by
        simpa only [Finset.subset_erase, Finset.subset_univ, true_and, not_not] using hT
      simp [coordinateFree, hi]) ω]
  apply Finset.sum_congr rfl
  intro T hT
  have hi : i ∉ T := (Finset.subset_erase.mp (Finset.mem_powerset.mp hT)).2
  simp [coordinateFree, hi]

/-- Evaluating the coordinate derivative sums its original coefficients over
the subsets omitting that coordinate. [OD14, §11.6, proof of (11.29)] -/
lemma coordinateDerivative_eval_sum {n : ℕ} {Ω : Type*}
    (F : MultilinearPolynomial n) (i : Fin n) (X : Fin n → Ω → ℝ) (ω : Ω) :
    evalMultilinearRV (coordinateDerivative F i) X ω =
      ∑ T ∈ (Finset.univ.erase i).powerset, F (insert i T) * ∏ j ∈ T, X j ω := by
  classical
  rw [MultilinearMoments.eval_supported (coordinateDerivative F i) X (Finset.univ.erase i)
    (fun T hT => by
      have hi : i ∈ T := by
        simpa only [Finset.subset_erase, Finset.subset_univ, true_and, not_not] using hT
      simp [coordinateDerivative_coeff, hi]) ω]
  apply Finset.sum_congr rfl
  intro T hT
  have hi : i ∉ T := (Finset.subset_erase.mp (Finset.mem_powerset.mp hT)).2
  simp [coordinateDerivative_coeff, hi]

/-- Input families agreeing off a coordinate have identical coordinate-free and
derivative evaluations at that coordinate. This is technical replacement glue. -/
lemma coordinate_parts_eq_of_off_coordinate {n : ℕ} {Ω : Type*}
    (F : MultilinearPolynomial n) (i : Fin n) (X Y : Fin n → Ω → ℝ)
    (hXY : ∀ j, j ≠ i → X j = Y j) :
    evalMultilinearRV (coordinateFree F i) X = evalMultilinearRV (coordinateFree F i) Y ∧
      evalMultilinearRV (coordinateDerivative F i) X =
        evalMultilinearRV (coordinateDerivative F i) Y := by
  constructor
  · exact MultilinearMoments.eval_eq_of_off_coordinate _ i X Y
      (fun S hi => by simp [coordinateFree, hi]) hXY
  · exact MultilinearMoments.eval_eq_of_off_coordinate _ i X Y
      (fun S hi => by simp [coordinateDerivative_coeff, hi]) hXY

/-- A multilinear polynomial is its coordinate-free part plus that input times
its coordinate derivative, on arbitrary real inputs.
[OD14, §11.6, proof of (11.29), coordinate decomposition] -/
lemma eval_coordinate_split {n : ℕ} {Ω : Type*}
    (F : MultilinearPolynomial n) (i : Fin n) (X : Fin n → Ω → ℝ) (ω : Ω) :
    evalMultilinearRV F X ω = evalMultilinearRV (coordinateFree F i) X ω +
      X i ω * evalMultilinearRV (coordinateDerivative F i) X ω := by
  classical
  rw [coordinateFree_eval_sum, coordinateDerivative_eval_sum]
  simpa only [Finset.insert_erase (Finset.mem_univ i),
    Finset.powerset_univ, evalMultilinearRV] using
      multilinear_sum_insert (s := Finset.univ.erase i) (Finset.notMem_erase i _) F X ω

/-- In an independent input family, a coordinate is independent of the joint
pair consisting of the coordinate-free part and coordinate derivative.
[OD14, §11.6, proof of (11.29)]

**Proof sketch.** Both polynomial parts are sums on the other coordinates.
Apply independence from a pair of polynomial sums on that disjoint index set. -/
lemma indep_coordinate_parts {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Fin n → Ω → ℝ}
    (hI : iIndepFun X μ) (hXm : ∀ j, AEMeasurable (X j) μ)
    (F : MultilinearPolynomial n) (i : Fin n) :
    IndepFun (X i) (fun ω =>
      (evalMultilinearRV (coordinateFree F i) X ω,
        evalMultilinearRV (coordinateDerivative F i) X ω)) μ := by
  classical
  simpa only [coordinateFree_eval_sum, coordinateDerivative_eval_sum] using
    MultilinearMoments.indep_sum_of_notMem hI hXm F (fun T => F (insert i T))
      (Finset.univ.erase i) i (Finset.notMem_erase i _)

end BooleanAnalysis.GaussianSpace.Invariance
