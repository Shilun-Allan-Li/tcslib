/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty, Mina Sha
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.Influence
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Norms

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier concentration on influential coordinates

## Main definitions

No new definitions.

## Main results

* `fourier_omission_le`: low-degree Fourier weight involving omitted coordinates is
  controlled by their influence threshold and a stable-influence estimate.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §9.6, Theorem 9.28 and Remark 9.29.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- If every coordinate outside `J` has influence at most `τ`, the degree-at-most-`k`
Fourier weight outside `J`, multiplied by `ρ^k`, is at most
`τ^((1-ρ)/(1+ρ)) I[f]` for Boolean `f` and `ρ ∈ [0,1]`.
[OD14, Thm. 9.28 and Remark 9.29, proofs]
This formulation includes `ρ = 0`, `ρ = 1`, `τ = 0`, and `k = 0`, using Lean's
real-power conventions.

**Proof sketch.** The weighted omission inequality charges each omitted Fourier set
to a coordinate outside `J`. Bound each resulting noisy contribution by its stable
influence, then apply hypercontractivity. Split the influence exponent as
`2/(1+ρ) = 1 + (1-ρ)/(1+ρ)`. Nonnegativity and the threshold bound control the second
factor by the corresponding power of `τ`. Sum the remaining influence factors and
bound their sum by total influence. -/
lemma fourier_omission_le {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (J : Finset (Fin n)) (k : ℕ) (ρ τ : ℝ) (hρ : ρ ∈ Set.Icc 0 1)
    (hτ : 0 ≤ τ) (houtside : ∀ i : Fin n, i ∉ J → influence i f ≤ τ) :
    ρ ^ k * (∑ S : Finset (Fin n),
      if S.card ≤ k ∧ ¬ S ⊆ J then fourierCoeff f S ^ 2 else 0) ≤
      τ ^ ((1 - ρ) / (1 + ρ)) * totalInfluence f :=
  (by
  classical
  let a : ℝ := (1 - ρ) / (1 + ρ)
  have ha : 0 ≤ a :=
    div_nonneg (sub_nonneg.mpr hρ.2) (by linarith [hρ.1])
  have hExp : 2 / (1 + ρ) = 1 + a := by
    dsimp [a]
    field_simp [show 1 + ρ ≠ 0 by linarith [hρ.1]]
    ring
  have hInf (i : Fin n) : 0 ≤ influence i f := by
    unfold influence
    exact ThresholdFunctions.expect_nonneg
      (fun x => div_nonneg (sq_nonneg _) (by norm_num))
  calc
    _ ≤ ∑ i : Fin n, if i ∈ J then 0 else
        ∑ S : Finset (Fin n),
          if i ∈ S then ρ ^ S.card * fourierCoeff f S ^ 2 else 0 :=
      FiniteNorms.weighted_lowDegree_omission_le
        (fun S => fourierCoeff f S ^ 2) (fun S => sq_nonneg _)
        J k ρ hρ.1 hρ.2
    _ ≤ ∑ i : Fin n, τ ^ a * influence i f := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ J
      · simp only [if_pos hi]
        exact mul_nonneg (Real.rpow_nonneg hτ _) (hInf i)
      · simp only [if_neg hi]
        calc
          _ ≤ KKL.noisyInfluence ρ i f := by
            unfold KKL.noisyInfluence
            apply Finset.sum_le_sum
            intro S _
            by_cases hiS : i ∈ S
            · simp only [if_pos hiS]
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_of_le_one hρ.1 hρ.2 (Nat.sub_le S.card 1))
                (sq_nonneg _)
            · simp only [if_neg hiS]
              exact le_rfl
          _ ≤ influence i f ^ (2 / (1 + ρ)) :=
            stableInfluence_le f hf i ρ hρ
          _ = influence i f * influence i f ^ a := by
            rw [hExp, Real.rpow_add_of_nonneg (hInf i) zero_le_one ha,
              Real.rpow_one]
          _ ≤ influence i f * τ ^ a :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (hInf i) (houtside i hi) ha) (hInf i)
          _ = τ ^ a * influence i f := mul_comm _ _
    _ = τ ^ a * totalInfluence f := by
      rw [← Finset.mul_sum]
      rfl
)

end BooleanAnalysis.Hypercontractivity
