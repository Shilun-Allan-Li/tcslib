/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Cube
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Duality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Noise interpolation for Bobkov's functional

## Main definitions

The noise operator is the existing Boolean Fourier multiplier.

## Main results

* `noiseOp_mem_unitInterval`: noise preserves the closed probability interval.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §2.4 and Theorem 11.55.
-/

open scoped BigOperators Topology

namespace BooleanAnalysis.GaussianSpace

open Hypercontractivity

/-- A noise operator with correlation in `[0,1]` preserves functions valued in
the closed probability interval. [OD14, §2.4]

**Proof sketch.** Each noisy value is a convex combination of the input values,
with the nonnegative transition kernel as its weights. -/
lemma noiseOp_mem_unitInterval {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (x : BoolCube n) : noiseOp ρ f x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [noiseOp_eq_kernel_sum]
  simpa only [smul_eq_mul] using (convex_Icc (0 : ℝ) 1).sum_mem
    (fun y _ => noiseKernel_nonneg hρ.1 hρ.2 x y)
    (noiseKernel_sum_right hρ.1 hρ.2 x) (fun y _ => hf y)

/-- The Boolean noise operator preserves two-term real linear combinations.
[OD14, §2.4, Fourier multiplier formula] -/
lemma noiseOp_linear_combination {n : ℕ} (ρ c d : ℝ) (f g : BooleanFunc n) :
    noiseOp ρ (fun x => c * f x + d * g x) =
      fun x => c * noiseOp ρ f x + d * noiseOp ρ g x := by
  funext x
  simp only [noiseOp_eq_kernel_sum, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    mul_assoc, mul_comm]

/-- Noise applied to a fixed restriction is the sum of the noised average and
the signed noised half-difference. [OD14, §2.4, coordinate decomposition] -/
lemma noiseOp_restrictLast_eq {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1))
    (bit : Bool) (x : BoolCube n) :
    noiseOp ρ (restrictLast f bit) x =
      noiseOp ρ (avgLast f) x + boolToSign bit * noiseOp ρ (diffLast f) x := by
  have hf : restrictLast f bit = fun y =>
      1 * avgLast f y + boolToSign bit * diffLast f y := by
    funext y
    cases bit <;>
      simp [boolToSign, restrictLast_false_eq, restrictLast_true_eq, sub_eq_add_neg]
  rw [hf, noiseOp_linear_combination]
  simp

/-- The last derivative of a noisy function is the correlation times the
noisy last-coordinate half-difference. [OD14, §2.4, coordinate decomposition] -/
lemma derivative_last_noise_snoc {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1))
    (x : BoolCube n) (bit : Bool) :
    derivative (Fin.last n) (noiseOp ρ f) (Fin.snoc x bit) =
      ρ * noiseOp ρ (diffLast f) x := by
  rw [derivative_last_snoc]
  dsimp only [diffLast, restrictLast]
  rw [noiseOp_snoc, noiseOp_snoc]
  simp only [boolToSign_false, boolToSign_true, one_mul, neg_one_mul]
  ring

/-- Restricting a noisy function in the last bit yields the noised average
plus the correlation times its signed noised half-difference.
[OD14, §2.4, coordinate decomposition] -/
lemma restrictLast_noiseOp_eq {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1)) (bit : Bool) :
    restrictLast (noiseOp ρ f) bit = fun x =>
      1 * noiseOp ρ (avgLast f) x + (boolToSign bit * ρ) * noiseOp ρ (diffLast f) x := by
  funext x
  simpa only [restrictLast, one_mul] using noiseOp_snoc ρ f x bit

/-- For each fixed bit, noise of that restriction equals the noised average
plus its signed noised half-difference, as an equality of functions. -/
lemma noiseOp_restrictLast_eq_fun {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1)) (bit : Bool) :
    noiseOp ρ (restrictLast f bit) = fun x =>
      1 * noiseOp ρ (avgLast f) x + boolToSign bit * noiseOp ρ (diffLast f) x := by
  funext x
  simpa only [one_mul] using noiseOp_restrictLast_eq ρ f bit x

/-- The two prefix-noised last-coordinate restrictions remain probability
values, expressed through their average and half-difference. -/
lemma noise_restriction_endpoints_mem {n : ℕ} (f : BooleanFunc (n + 1))
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (x : BoolCube n) :
    (noiseOp ρ (avgLast f) x + noiseOp ρ (diffLast f) x ∈ Set.Icc (0 : ℝ) 1) ∧
      (noiseOp ρ (avgLast f) x - noiseOp ρ (diffLast f) x ∈ Set.Icc (0 : ℝ) 1) := by
  constructor
  · simpa only [noiseOp_restrictLast_eq, boolToSign_false, one_mul] using
      noiseOp_mem_unitInterval (restrictLast f false) (fun y => hf _) hρ x
  · simpa only [noiseOp_restrictLast_eq, boolToSign_true, neg_one_mul, ← sub_eq_add_neg] using
      noiseOp_mem_unitInterval (restrictLast f true) (fun y => hf _) hρ x

end BooleanAnalysis.GaussianSpace
