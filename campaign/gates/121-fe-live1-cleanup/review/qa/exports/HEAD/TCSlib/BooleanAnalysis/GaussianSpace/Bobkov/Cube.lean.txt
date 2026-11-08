/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Decomposition
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cube calculus for Bobkov's inequality

## Main definitions

The Boolean derivatives, expectation, and last-coordinate restrictions are reused.

## Main results

Derivative restriction identities and the triangle inequality for expected lengths.

## References

* [Bob97] S. G. Bobkov, *An isoperimetric inequality on the discrete cube, and an
  elementary proof of the isoperimetric inequality in Gauss space*, Annals of
  Probability 25 (1997), 206–214, Lemma 1.
* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, equation (11.15).
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

open Hypercontractivity ThresholdFunctions

/-- A derivative in an earlier coordinate commutes with fixing the last coordinate.
[Bob97, Lemma 1 (proof)] -/
lemma derivative_restrictLast {n : ℕ} (f : BooleanFunc (n + 1))
    (i : Fin n) (b : Bool) (x : BoolCube n) :
    derivative i (restrictLast f b) x = derivative i.castSucc f (Fin.snoc x b) := by
  simp only [derivative, restrictLast, Fin.snoc_update]

/-- The last discrete derivative is the half-difference of the two restrictions,
independently of the value fixed in that coordinate. [Bob97, Lemma 1 (proof)] -/
lemma derivative_last_snoc {n : ℕ} (f : BooleanFunc (n + 1)) (b : Bool) (x : BoolCube n) :
    derivative (Fin.last n) f (Fin.snoc x b) = diffLast f x := by
  simp only [derivative, Fin.update_snoc_last, diffLast, restrictLast]

/-- The squared gradient splits into the squared gradient of a restriction and
the squared last-coordinate half-difference. [Bob97, Lemma 1 (proof)] -/
lemma sum_sq_derivative_snoc {n : ℕ} (f : BooleanFunc (n + 1)) (b : Bool) (x : BoolCube n) :
    (∑ i : Fin (n + 1), (derivative i f (Fin.snoc x b)) ^ 2) =
      (∑ i : Fin n, (derivative i (restrictLast f b) x) ^ 2) + (diffLast f x) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [← derivative_restrictLast, derivative_last_snoc]

/-- The mean of the last-coordinate half-difference is the half-difference of
the means of the two restrictions. [Bob97, Lemma 1 (proof)] -/
lemma expect_diffLast {n : ℕ} (f : BooleanFunc (n + 1)) :
    expect (diffLast f) = (expect (restrictLast f false) - expect (restrictLast f true)) / 2 := by
  unfold diffLast expect
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  ring

/-- The Euclidean length of two expected real coordinates is at most the
expected length of the coordinate pair. [Bob97, Lemma 1 (proof)]

**Proof sketch.** Regard the pair as a complex number and apply the triangle
inequality for its finite expectation. -/
lemma sqrt_expect_sq_add_sq_le_expect_sqrt {n : ℕ} (u v : BooleanFunc n) :
    Real.sqrt ((expect u) ^ 2 + (expect v) ^ 2) ≤
      expect (fun x => Real.sqrt ((u x) ^ 2 + (v x) ^ 2)) := by
  simp only [expect_eq_fintypeExpect]
  have heq : (𝔼 x : BoolCube n, (⟨u x, v x⟩ : ℂ)) =
      (⟨𝔼 x : BoolCube n, u x, 𝔼 x : BoolCube n, v x⟩ : ℂ) := by
    apply Complex.ext <;> simp
  have h := RCLike.norm_expect_le (K := ℂ) (s := Finset.univ)
    (f := fun x : BoolCube n => (⟨u x, v x⟩ : ℂ))
  rw [heq] at h
  simpa only [Complex.norm_def, Complex.normSq_mk, sq] using h

/-- A midpoint bound for one nonnegative coordinate remains valid after
adjoining arbitrary symmetrically varying Euclidean coordinates.
[OD14, §11.4, Exercise 11.24]

**Proof sketch.** Adjoin the scalar coordinate to a finite Euclidean vector and
apply the triangle inequality to the two endpoint vectors. -/
lemma carried_midpoint {m : ℕ} (u v : Fin m → ℝ) (A B C : ℝ)
    (hA : 0 ≤ A) (h : A ≤ (B + C) / 2) :
    Real.sqrt (A ^ 2 + ∑ j, u j ^ 2) ≤
      (Real.sqrt (B ^ 2 + ∑ j, (u j + v j) ^ 2) +
        Real.sqrt (C ^ 2 + ∑ j, (u j - v j) ^ 2)) / 2 := by
  let p : EuclideanSpace ℝ (Fin (m + 1)) :=
    WithLp.toLp 2 (Fin.cons B (fun j => u j + v j))
  let q : EuclideanSpace ℝ (Fin (m + 1)) :=
    WithLp.toLp 2 (Fin.cons C (fun j => u j - v j))
  let w : EuclideanSpace ℝ (Fin (m + 1)) :=
    WithLp.toLp 2 (Fin.cons ((B + C) / 2) u)
  have hw : w = (1 / 2 : ℝ) • (p + q) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [w, p, q]
      ring
    · simp [w, p, q]
      ring
  have hn : ‖w‖ ≤ (‖p‖ + ‖q‖) / 2 := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith [norm_add_le p q]
  have hsq : A ^ 2 ≤ ((B + C) / 2) ^ 2 := by nlinarith
  refine (Real.sqrt_le_sqrt (add_le_add_right hsq _)).trans ?_
  simpa [w, p, q, EuclideanSpace.norm_eq, Fin.sum_univ_succ,
    Real.norm_eq_abs, sq_abs] using hn

/-- A discrete derivative preserves two-term real linear combinations.
[OD14, §2.2, discrete derivatives] -/
lemma derivative_linear_combination {n : ℕ} (i : Fin n)
    (f g : BooleanFunc n) (c d : ℝ) :
    derivative i (fun x => c * f x + d * g x) =
      fun x => c * derivative i f x + d * derivative i g x := by
  change derivative i (c • f + d • g) = c • derivative i f + d • derivative i g
  rw [derivative_add, derivative_smul, derivative_smul]

end BooleanAnalysis.GaussianSpace
