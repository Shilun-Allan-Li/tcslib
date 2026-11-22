/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Noise
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Elementary
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The stability cost of Boolean smoothing

## Main definitions

The existing Boolean noise and Fourier coefficients are reused.

## Main results

* `noiseStability_sub_noiseOp_le`: smoothing costs at most `2δ/(1-ρ)`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, proof of (11.39).
-/

open scoped BigOperators
namespace BooleanAnalysis.GaussianSpace.MajorityIsStablest
open ThresholdFunctions Hypercontractivity

/-- Smoothing a unit-interval-valued function loses at most `2δ/(1-ρ)` stability.
[OD14, §11.7, proof of (11.39)]

**Proof sketch.** Bernoulli's inequality bounds each coefficient loss by `2kδ`.
The first k terms of a geometric series dominate `kρ^k`, hence that quantity is
at most `1/(1-ρ)`. Sum the coefficient bounds and use Parseval and the range. -/
lemma noiseStability_sub_noiseOp_le {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {ρ δ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    noiseStability ρ f - noiseStability ρ (noiseOp (1 - δ) f) ≤
      2 * δ / (1 - ρ) := by
  classical
  have hc : 0 ≤ 2 * δ / (1 - ρ) :=
    div_nonneg (mul_nonneg (by norm_num) hδ.1) (sub_nonneg.mpr hρ.2.le)
  have hcoeff (k : ℕ) :
      ρ ^ k * (1 - ((1 - δ) ^ k) ^ 2) ≤ 2 * δ / (1 - ρ) := by
    have hbern : 1 - ((1 - δ) ^ k) ^ 2 ≤ 2 * (k : ℝ) * δ := by
      have hb := one_add_mul_sub_le_pow (a := 1 - δ)
        (by linarith [hδ.2] : -1 ≤ 1 - δ) (k * 2)
      rw [pow_mul] at hb
      push_cast at hb
      nlinarith
    have hgeom : (k : ℝ) * ρ ^ k ≤ ∑ j ∈ Finset.range k, ρ ^ j := by
      calc
        (k : ℝ) * ρ ^ k = ∑ _j ∈ Finset.range k, ρ ^ k := by simp
        _ ≤ _ := Finset.sum_le_sum fun j hj =>
          pow_le_pow_of_le_one hρ.1.le hρ.2.le
            (Finset.mem_range.mp hj).le
    have hmul : ((k : ℝ) * ρ ^ k) * (1 - ρ) ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_right hgeom
        (sub_nonneg.mpr hρ.2.le)
      rw [geom_sum_mul_neg] at hm
      exact hm.trans (sub_le_self _ (pow_nonneg hρ.1.le _))
    apply (le_div_iff₀ (sub_pos.mpr hρ.2)).mpr
    have hb := mul_le_mul_of_nonneg_left hbern (pow_nonneg hρ.1.le k)
    have hb' := mul_le_mul_of_nonneg_right hb
      (sub_nonneg.mpr hρ.2.le)
    have hm' := mul_le_mul_of_nonneg_left hmul
      (show 0 ≤ (2 : ℝ) * δ from mul_nonneg (by norm_num) hδ.1)
    nlinarith
  have henergy : (∑ S : Finset (Fin n), fourierCoeff f S ^ 2) ≤ 1 := by
    rw [← parseval]
    change expect (fun x => f x * f x) ≤ 1
    calc
      _ ≤ expect (fun _ : BoolCube n => (1 : ℝ)) :=
        expect_mono fun x => by
          have hx := hf x
          nlinarith [hx.1, hx.2]
      _ = 1 := expect_const 1
  calc
    noiseStability ρ f - noiseStability ρ (noiseOp (1 - δ) f) =
        ∑ S : Finset (Fin n),
          (ρ ^ S.card * (1 - ((1 - δ) ^ S.card) ^ 2)) *
            fourierCoeff f S ^ 2 := by
      simp only [noiseStability, stability_formula, noiseOp_fourier,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ ≤ ∑ S : Finset (Fin n),
        (2 * δ / (1 - ρ)) * fourierCoeff f S ^ 2 :=
      Finset.sum_le_sum fun S _ =>
        mul_le_mul_of_nonneg_right (hcoeff S.card) (sq_nonneg _)
    _ = (2 * δ / (1 - ρ)) *
        ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (2 * δ / (1 - ρ)) * 1 :=
      mul_le_mul_of_nonneg_left henergy hc
    _ = 2 * δ / (1 - ρ) := mul_one _

/-- Noisy influence increases with nonnegative correlation. [OD14, §2.4] -/
lemma noisyInfluence_mono {n : ℕ} (f : BooleanFunc n) (i : Fin n)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    KKL.noisyInfluence a i f ≤ KKL.noisyInfluence b i f := by
  classical
  unfold KKL.noisyInfluence
  apply Finset.sum_le_sum
  intro S _
  split_ifs
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab _) (sq_nonneg _)
  · exact le_rfl

/-- Unit-interval-valued functions have noise stability at most one.
[OD14, §2.4] -/
lemma noiseStability_le_one {n : ℕ} (f : BooleanFunc n)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : noiseStability ρ f ≤ 1 := by
  change expect (fun x => f x * noiseOp ρ f x) ≤ 1
  calc
    _ ≤ expect (fun _ : BoolCube n => (1 : ℝ)) := expect_mono fun x =>
      (mul_le_mul (hf x).2 (noiseOp_mem_unitInterval f hf hρ x).2
        (noiseOp_mem_unitInterval f hf hρ x).1 (by norm_num : (0 : ℝ) ≤ 1)).trans
        (by norm_num)
    _ = 1 := expect_const 1

end BooleanAnalysis.GaussianSpace.MajorityIsStablest
