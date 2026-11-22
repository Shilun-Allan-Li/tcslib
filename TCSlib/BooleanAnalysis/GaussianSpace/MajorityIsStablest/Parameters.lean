/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logarithmic parameters for Majority Is Stablest

## Main definitions

No new definitions.

## Main results

* `scalar_parameters`: either the final error is at least one, or there is an
  admissible smoothing parameter which bounds both analytic errors.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, proof of (11.39).
-/

open Filter

namespace BooleanAnalysis.GaussianSpace.MajorityIsStablest

/-- A universal constant absorbs the smoothing and invariance errors at the
logarithmic scale, with a separate trivial regime. [OD14, §11.7, proof of (11.39)]

**Proof sketch.** Since log L / L tends to zero, choose a universal cutoff above
which δ = 6 log L / L is admissible. Then ε^(δ/6) = 1/L. Below that cutoff,
enlarge the constant so that the claimed error is at least one. -/
theorem scalar_parameters (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε L r : ℝ), 0 < ε → 2 ≤ L →
      Real.log ε = -L → r ∈ Set.Ioo (0 : ℝ) 1 →
      1 ≤ C * Real.log L / ((1-r)*L) ∨
      ∃ δ : ℝ, 1/L ≤ δ ∧ 0 < δ ∧ δ ≤ 1/20 ∧
        2*δ/(1-r) + A*ε^(δ/6) ≤ C*Real.log L/((1-r)*L) := by
  have ht : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/120)))
  let B : ℝ := max 2 M
  refine ⟨12 + 2*A + 2*B, ?_, ?_⟩
  · have : 2 ≤ B := le_max_left _ _
    linarith
  intro ε L r hε hL hεL hr
  have hLp : 0 < L := by linarith
  have hq : 0 < 1-r := sub_pos.mpr hr.2
  have hlog : 1/2 ≤ Real.log L := by
    have hi : L⁻¹ ≤ 1/2 := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hLp).2 (by linarith)
    have := Real.one_sub_inv_le_log_of_pos hLp
    linarith
  have hB : 2 ≤ B := le_max_left _ _
  by_cases hlarge : B ≤ L
  · right
    let δ : ℝ := 6 * Real.log L / L
    have hδlo : 1/L ≤ δ := by
      dsimp [δ]
      apply (div_le_div_iff_of_pos_right hLp).2
      linarith
    have hδpos : 0 < δ := lt_of_lt_of_le (one_div_pos.mpr hLp) hδlo
    have hδhi : δ ≤ 1/20 := by
      have hsmall := hM L ((le_max_right 2 M).trans hlarge)
      dsimp [δ]
      rw [div_le_iff₀ hLp]
      have hs := (div_lt_iff₀ hLp).1 hsmall
      linarith
    refine ⟨δ, hδlo, hδpos, hδhi, ?_⟩
    have hpower : ε ^ (δ/6) = 1/L := by
      rw [Real.rpow_def_of_pos hε, hεL]
      have hexp : -L * (δ/6) = -Real.log L := by
        dsimp [δ]
        field_simp
      rw [hexp, Real.exp_neg, Real.exp_log hLp]
      simp
    rw [hpower]
    apply (le_div_iff₀ (mul_pos hq hLp)).2
    have hcancel : (2*δ/(1-r) + A*(1/L))*((1-r)*L) =
        12*Real.log L + A*(1-r) := by
      dsimp [δ]
      field_simp
      ring
    rw [hcancel]
    nlinarith [mul_nonneg hA hr.1.le,
      mul_nonneg (by linarith : 0 ≤ B) (by linarith : 0 ≤ Real.log L)]
  · left
    apply (le_div_iff₀ (mul_pos hq hLp)).2
    have hLB : L ≤ B := le_of_lt (lt_of_not_ge hlarge)
    have hqr : (1-r)*L ≤ L := by nlinarith [hr.1]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 12 + 2*A)
      (by linarith : 0 ≤ Real.log L)]

end BooleanAnalysis.GaussianSpace.MajorityIsStablest
