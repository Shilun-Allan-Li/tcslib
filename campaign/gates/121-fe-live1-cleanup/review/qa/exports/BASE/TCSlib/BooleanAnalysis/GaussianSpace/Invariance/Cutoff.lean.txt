/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Smoothing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Smooth half-line cutoffs

## Main definitions

An internal clipped affine ramp is smoothed using the existing interval average.

## Main results

Positive-width smooth cutoffs of a half-line have explicit transition widths
and derivative bounds.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, proof of Corollary 11.70.
-/

open MeasureTheory
open scoped NNReal

namespace BooleanAnalysis.GaussianSpace.Invariance

/-- The affine transition from one to zero on the interval `[v-η,v]`.
[OD14, Cor. 11.70 (proof), interval-average adaptation] -/
private noncomputable def cutoffRamp (v η x : ℝ) : ℝ :=
  max 0 (min 1 ((v - x) / η))

/-- A clipped affine ramp has Lipschitz constant equal to its inverse width.
[OD14, Cor. 11.70 (proof)] -/
private theorem lipschitz_cutoffRamp {η : ℝ} (hη : 0 < η) (v : ℝ) :
    LipschitzWith ⟨1 / η, by positivity⟩ (cutoffRamp v η) := by
  have haff : LipschitzWith ⟨1 / η, by positivity⟩ (fun x : ℝ => (v - x) / η) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_mk]
    rw [← sub_div, show v - x - (v - y) = -(x - y) by ring,
      abs_div, abs_neg, abs_of_pos hη]
    exact le_of_eq (by ring)
  exact (haff.const_min 1).const_max 0

/-- The ramp stays in `[0,1]` and is constant outside its transition interval.
[OD14, Cor. 11.70 (proof)] -/
private theorem cutoffRamp_bounds {η : ℝ} (hη : 0 < η) (v : ℝ) :
    (∀ x, cutoffRamp v η x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, x + η ≤ v → cutoffRamp v η x = 1) ∧
      (∀ x, v ≤ x → cutoffRamp v η x = 0) := by
  refine ⟨fun x => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩, ?_, ?_⟩
  · intro x hx
    have h : 1 ≤ (v - x) / η := (le_div_iff₀ hη).mpr (by linarith)
    simp only [cutoffRamp, min_eq_left h, max_eq_right zero_le_one]
  · intro x hx
    have h : (v - x) / η ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hη.le
    simp only [cutoffRamp, min_eq_right (h.trans zero_le_one), max_eq_left h]

/-- A half-line has a smooth cutoff with explicit transition width and derivative
bound. [OD14, Cor. 11.70 (proof), interval-average adaptation]

**Proof sketch.** Start with a clipped affine ramp shifted past the half-line.
Repeated averaging adds derivatives. The integral mean value property retains
the range and constant regions, and the endpoint-difference formula bounds derivatives. -/
theorem exists_contDiff_cutoff (m : ℕ) (u : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (m + 1 : ℕ) φ ∧
      (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, x ≤ u → φ x = 1) ∧
      (∀ x, u + ((m + 2 : ℕ) : ℝ) * η ≤ x → φ x = 0) ∧
      ∀ x, |iteratedDeriv (m + 1) φ x| ≤ (2 : ℝ) ^ m / η ^ (m + 1) := by
  let v := u + ((m + 2 : ℕ) : ℝ) * η
  have hlip := lipschitz_cutoffRamp hη v
  obtain ⟨hC, _, _, hD⟩ := intervalSmooth_iterate_bounds hη hlip m
  obtain ⟨hrange, hleft, hright⟩ := cutoffRamp_bounds hη v
  refine ⟨((intervalSmooth η)^[m + 1]) (cutoffRamp v η), hC, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy, he⟩ :=
      intervalSmooth_iterate_exists_value hη hlip.continuous (m + 1) x
    rw [he]
    exact hrange y
  · intro x hx
    obtain ⟨y, hy, he⟩ :=
      intervalSmooth_iterate_exists_value hη hlip.continuous (m + 1) x
    rw [he]
    apply hleft
    dsimp [v]
    push_cast at hy ⊢
    nlinarith [hy.2]
  · intro x hx
    obtain ⟨y, hy, he⟩ :=
      intervalSmooth_iterate_exists_value hη hlip.continuous (m + 1) x
    rw [he]
    exact hright y (hx.trans hy.1)
  · intro x
    calc
      _ ≤ (1 / η) * (2 / η) ^ m := hD x
      _ = _ := by rw [div_pow, pow_succ]; ring

end BooleanAnalysis.GaussianSpace.Invariance
