/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Interpolation
import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Noise
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Tensorization of Bobkov's noise interpolation

## Main definitions

* `BobkovInterpolation.extendedFunctional`: the profile-gradient length with carried coordinates.

## Main results

The symmetric-pair contraction tensorizes over the Boolean cube, preserving
arbitrary extra coordinates under noise. The empty extra vector specializes to
Bobkov's functional.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, Theorem 11.55 and Exercise 11.24.
-/

open scoped BigOperators Topology
open Set Filter

namespace BooleanAnalysis.GaussianSpace.BobkovInterpolation

open Hypercontractivity ThresholdFunctions

/-- The extended Bobkov functional is the expected profile-gradient length
with an arbitrary finite vector of extra real-valued coordinates.
[OD14, Theorem 11.55, Exercise 11.24]
The extra vector is the induction strengthening needed for noise interpolation;
the profile is left as a parameter to expose the two-point assumption. -/
noncomputable def extendedFunctional {n m : ℕ} (P : ℝ → ℝ) (f : BooleanFunc n)
    (g : Fin m → BooleanFunc n) : ℝ :=
  expect fun x => Real.sqrt
    (P (f x) ^ 2 + (∑ i : Fin n, (derivative i f x) ^ 2) + ∑ j : Fin m, (g j x) ^ 2)

/-- The gradient coordinates followed by the extra coordinates at a cube point. -/
noncomputable def lengthVector {n m : ℕ} (f : BooleanFunc n) (g : Fin m → BooleanFunc n)
    (x : BoolCube n) : Fin (n + m) → ℝ :=
  Fin.append (fun i => derivative i f x) (fun j => g j x)

/-- The squared length of the combined vector is the sum of the squared
gradient and extra-coordinate lengths. -/
lemma sum_sq_lengthVector {n m : ℕ} (f : BooleanFunc n) (g : Fin m → BooleanFunc n)
    (x : BoolCube n) :
    (∑ j : Fin (n + m), (lengthVector f g x j) ^ 2) =
      (∑ i : Fin n, (derivative i f x) ^ 2) + ∑ j : Fin m, (g j x) ^ 2 := by
  rw [Fin.sum_univ_add]
  simp only [lengthVector, Fin.append_left, Fin.append_right]

/-- Restricting the integrand separates its last derivative from the combined
prefix-gradient and extra-coordinate vector. -/
lemma extended_length_snoc {n m : ℕ} (P : ℝ → ℝ) (f : BooleanFunc (n + 1))
    (g : Fin m → BooleanFunc (n + 1)) (x : BoolCube n) (bit : Bool) :
    Real.sqrt (P (f (Fin.snoc x bit)) ^ 2 +
      (∑ i : Fin (n + 1), (derivative i f (Fin.snoc x bit)) ^ 2) +
        ∑ j : Fin m, (g j (Fin.snoc x bit)) ^ 2) =
    Real.sqrt (P (restrictLast f bit x) ^ 2 + diffLast f x ^ 2 +
      ∑ j : Fin (n + m),
        (lengthVector (restrictLast f bit) (fun j => restrictLast (g j) bit) x j) ^ 2) := by
  rw [sum_sq_derivative_snoc, sum_sq_lengthVector]
  simp only [restrictLast]
  congr 1
  ring

/-- The combined gradient and carried-coordinate vector preserves real
linear combinations. -/
lemma lengthVector_linear_combination {n m : ℕ} (f₁ f₂ : BooleanFunc n)
    (g₁ g₂ : Fin m → BooleanFunc n) (c d : ℝ) (x : BoolCube n) :
    lengthVector (fun y => c * f₁ y + d * f₂ y)
      (fun j y => c * g₁ j y + d * g₂ j y) x =
      fun k => c * lengthVector f₁ g₁ x k + d * lengthVector f₂ g₂ x k := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [lengthVector, Fin.append_left, derivative_linear_combination]
  · simp only [lengthVector, Fin.append_right]

/-- The gradient and extra-coordinate vector of a prefix-noised restriction
decomposes into the corresponding noised average and half-difference vectors. -/
lemma lengthVector_noise_restriction {n m : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1))
    (g : Fin m → BooleanFunc (n + 1)) (x : BoolCube n) (bit : Bool) :
    lengthVector (noiseOp ρ (restrictLast f bit))
      (fun j => noiseOp ρ (restrictLast (g j) bit)) x =
    fun k => lengthVector (noiseOp ρ (avgLast f)) (fun j => noiseOp ρ (avgLast (g j))) x k +
      boolToSign bit *
        lengthVector (noiseOp ρ (diffLast f)) (fun j => noiseOp ρ (diffLast (g j))) x k := by
  simp_rw [noiseOp_restrictLast_eq_fun]
  rw [lengthVector_linear_combination]
  simp only [one_mul]

/-- Restricting the gradient and extra-coordinate vector after full noise
multiplies its half-difference part by the correlation. -/
lemma lengthVector_restrictLast_noiseOp {n m : ℕ} (ρ : ℝ)
    (f : BooleanFunc (n + 1)) (g : Fin m → BooleanFunc (n + 1))
    (bit : Bool) (x : BoolCube n) :
    lengthVector (restrictLast (noiseOp ρ f) bit)
      (fun j => restrictLast (noiseOp ρ (g j)) bit) x =
      fun k => lengthVector (noiseOp ρ (avgLast f))
        (fun j => noiseOp ρ (avgLast (g j))) x k +
        (boolToSign bit * ρ) * lengthVector (noiseOp ρ (diffLast f))
          (fun j => noiseOp ρ (diffLast (g j))) x k := by
  simp_rw [restrictLast_noiseOp_eq]
  rw [lengthVector_linear_combination]
  simp only [one_mul]

/-- Fixing the last cube coordinate turns its half-difference into one more
carried coordinate of the restricted extended functional.
[OD14, Theorem 11.55, coordinate induction] -/
lemma extendedFunctional_restrictLast {n m : ℕ} (P : ℝ → ℝ)
    (f : BooleanFunc (n + 1)) (g : Fin m → BooleanFunc (n + 1)) :
    extendedFunctional P f g =
      (extendedFunctional P (restrictLast f false)
          (Fin.cons (diffLast f) (fun j => restrictLast (g j) false)) +
        extendedFunctional P (restrictLast f true)
          (Fin.cons (diffLast f) (fun j => restrictLast (g j) true))) / 2 := by
  unfold extendedFunctional
  rw [expect_succ_eq]
  congr 2 <;> congr 1 <;> funext x
  all_goals
    dsimp only [restrictLast]
    rw [sum_sq_derivative_snoc]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, restrictLast,
      add_assoc, add_left_comm, add_comm]

/-- Splitting the last coordinate of a noised function gives the symmetric
pair at the current correlation, with its last derivative in the clock term.
[OD14, Theorem 11.55, noise interpolation]

**Proof sketch.** Average the two last-coordinate restrictions. Their values
and combined vectors are the noised average plus or minus the correlation times
the noised half-difference. The last derivative is the same in both branches. -/
lemma extendedFunctional_noise_pair {n m : ℕ} (P : ℝ → ℝ) (ρ : ℝ)
    (f : BooleanFunc (n + 1)) (g : Fin m → BooleanFunc (n + 1)) :
    extendedFunctional P (noiseOp ρ f) (fun j => noiseOp ρ (g j)) =
      expect (fun x => pairLength P
        (noiseOp ρ (avgLast f) x) (noiseOp ρ (diffLast f) x)
        (lengthVector (noiseOp ρ (avgLast f))
          (fun j => noiseOp ρ (avgLast (g j))) x)
        (lengthVector (noiseOp ρ (diffLast f))
          (fun j => noiseOp ρ (diffLast (g j))) x)
        ρ ((ρ * noiseOp ρ (diffLast f) x) ^ 2)) := by
  unfold extendedFunctional
  rw [expect_succ_eq_iterated]
  apply congrArg expect
  funext x
  rw [extended_length_snoc, extended_length_snoc]
  have hd : diffLast (noiseOp ρ f) x = ρ * noiseOp ρ (diffLast f) x := by
    simpa only [derivative_last_snoc] using derivative_last_noise_snoc ρ f x false
  rw [hd, lengthVector_restrictLast_noiseOp, lengthVector_restrictLast_noiseOp]
  simp only [pairLength, restrictLast_noiseOp_eq,
    boolToSign_false, boolToSign_true, one_mul, neg_mul, sub_eq_add_neg]
  ring

/-- At full last-coordinate correlation, the symmetric-pair expectation is
the average of the two prefix-noised extended functionals. The noised last
half-difference is carried as an extra coordinate.
[OD14, Theorem 11.55, coordinate induction]

**Proof sketch.** The two endpoint vectors are the prefix-noised restrictions.
Expand their squared lengths and carry the half-difference as the first extra
coordinate. Linearity of the uniform expectation gives the asserted average. -/
lemma expect_pairLength_one {n m : ℕ} (P : ℝ → ℝ) (ρ : ℝ)
    (f : BooleanFunc (n + 1)) (g : Fin m → BooleanFunc (n + 1)) :
    expect (fun x => pairLength P
      (noiseOp ρ (avgLast f) x) (noiseOp ρ (diffLast f) x)
      (lengthVector (noiseOp ρ (avgLast f)) (fun j => noiseOp ρ (avgLast (g j))) x)
      (lengthVector (noiseOp ρ (diffLast f)) (fun j => noiseOp ρ (diffLast (g j))) x)
      1 ((noiseOp ρ (diffLast f) x) ^ 2)) =
      (extendedFunctional P (noiseOp ρ (restrictLast f false))
        (Fin.cons (noiseOp ρ (diffLast f)) (fun j => noiseOp ρ (restrictLast (g j) false))) +
      extendedFunctional P (noiseOp ρ (restrictLast f true))
        (Fin.cons (noiseOp ρ (diffLast f)) (fun j => noiseOp ρ (restrictLast (g j) true)))) / 2 := by
  have hvec (x : BoolCube n) (bit : Bool) := sum_sq_lengthVector
    (noiseOp ρ (restrictLast f bit)) (fun j => noiseOp ρ (restrictLast (g j) bit)) x
  simp_rw [lengthVector_noise_restriction] at hvec
  have hp (x : BoolCube n) := hvec x false
  have hm (x : BoolCube n) := hvec x true
  have hfp (x : BoolCube n) := noiseOp_restrictLast_eq ρ f false x
  have hfm (x : BoolCube n) := noiseOp_restrictLast_eq ρ f true x
  simp only [boolToSign_false, boolToSign_true, one_mul, neg_one_mul,
    ← sub_eq_add_neg] at hp hm hfp hfm
  unfold pairLength extendedFunctional
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, one_mul]
  simp_rw [hp, hm, ← hfp, ← hfm]
  simp only [add_assoc, add_left_comm, add_comm]
  unfold expect
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- Simultaneously applying Boolean noise to a probability-valued function
and arbitrary carried coordinates decreases the extended profile-gradient length,
whenever the continuous nonnegative profile satisfies the scalar two-point bound.
[OD14, Theorem 11.55, Exercise 11.24]
This strengthens the source formulation by allowing any such profile and extra vector.

**Proof sketch.** Induct on the cube dimension uniformly in the number of carried
coordinates. Split off the last bit and apply symmetric-pair contraction pointwise.
The endpoint pair consists of the prefix-noised restrictions, with the noised last
half-difference carried as one extra coordinate. Apply the induction hypothesis to
each restriction and average. In dimension zero the noise operator is the identity. -/
lemma extendedFunctional_noise_le {n m : ℕ} {P : ℝ → ℝ}
    (hcont : ContinuousOn P (Icc (0 : ℝ) 1))
    (hP : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ P x)
    (htwo : ∀ a b : ℝ, a + b ∈ Icc (0 : ℝ) 1 → a - b ∈ Icc (0 : ℝ) 1 →
      P a ≤ (Real.sqrt (P (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (P (a - b) ^ 2 + b ^ 2)) / 2)
    (f : BooleanFunc n) (g : Fin m → BooleanFunc n)
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    extendedFunctional P (noiseOp ρ f) (fun j => noiseOp ρ (g j)) ≤
      extendedFunctional P f g := by
  induction n generalizing m with
  | zero =>
      simp only [noiseOp_dim_zero]
      exact le_rfl
  | succ n ih =>
      rw [extendedFunctional_noise_pair]
      refine (expect_mono (fun x => pairLength_contraction hcont hP htwo _ _
        (noise_restriction_endpoints_mem f hf hρ x).1
        (noise_restriction_endpoints_mem f hf hρ x).2 hρ)).trans ?_
      rw [expect_pairLength_one, extendedFunctional_restrictLast]
      have haux (bit : Bool) :
          extendedFunctional P (noiseOp ρ (restrictLast f bit))
            (Fin.cons (noiseOp ρ (diffLast f))
              (fun j => noiseOp ρ (restrictLast (g j) bit))) ≤
          extendedFunctional P (restrictLast f bit)
            (Fin.cons (diffLast f) (fun j => restrictLast (g j) bit)) := by
        convert ih (restrictLast f bit)
          (Fin.cons (diffLast f) (fun j => restrictLast (g j) bit))
          (fun x => hf (Fin.snoc x bit)) using 1
        congr 1
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      exact div_le_div_of_nonneg_right (add_le_add (haux false) (haux true)) zero_le_two

end BooleanAnalysis.GaussianSpace.BobkovInterpolation
