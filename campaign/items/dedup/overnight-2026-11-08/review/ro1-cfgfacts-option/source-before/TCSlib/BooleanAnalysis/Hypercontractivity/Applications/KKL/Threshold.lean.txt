/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty, Mina Sha
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Junta
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Comparison
import TCSlib.BooleanAnalysis.ThresholdFunctions.NoiseStability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Junta approximation of linear threshold functions

## Main definitions

No new definitions. The Boolean function and its approximant share the original cube.

## Main results

* `linearThreshold_fourier_cutoff`: Peres gives a universal reciprocal-square cutoff.
* `linearThreshold_junta_size_bound`: absorb the optimized junta prefactor.
* `linearThreshold_junta`: an LTF admits a junta approximation with coordinate count
  controlled by its total influence, error and exponent slack.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §5.5, Peres's Theorem; §9.6, Remark 9.29 and Corollary 9.31.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- An absolute constant `B ≥ 1` gives every ±1-valued linear threshold function
Fourier weight at most `ε` above some natural degree `k ≤ B / ε²`, uniformly in
the dimension and `0 < ε ≤ 1/2`.
[OD14, §5.5, Peres's Theorem; Cor. 9.31, proof]
This formulation makes the natural cutoff and the lower bound on `B` explicit.

**Proof sketch.** Let `A ≥ 0` be Peres's noise-sensitivity constant. Set
`B = 9(A + 1)²`, choose `δ = (ε / (3(A + 1)))²`, and take `k = ⌊1/δ⌋`.
The Fourier tail is at most three times the noise sensitivity, which Peres's
estimate bounds by `3A√δ ≤ ε`. The floor bound gives `k ≤ B / ε²`. -/
lemma linearThreshold_fourier_cutoff :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f →
        ThresholdFunctions.IsLinearThreshold f →
        ∀ ε : ℝ, ε ∈ Set.Ioc 0 (1 / 2) →
          ∃ k : ℕ, (k : ℝ) ≤ B / ε ^ 2 ∧
            ThresholdFunctions.fourierWeightAbove k f ≤ ε :=
  (by
  classical
  obtain ⟨A, hA, hPeres⟩ := ThresholdFunctions.peres_theorem
  refine ⟨9 * (A + 1) ^ 2, ?_, ?_⟩
  · nlinarith only [hA, sq_nonneg A]
  · intro n f hf hltf ε hε
    have hεpos : 0 < ε := hε.1
    let r : ℝ := ε / (3 * (A + 1))
    have hrpos : 0 < r := by
      dsimp [r]
      positivity
    have hrle : r ≤ 1 / 2 := by
      dsimp [r]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith only [hA, hε.2]
    let δ : ℝ := r ^ 2
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδle : δ ≤ 1 / 2 := by
      have hsq := pow_le_pow_left₀ hrpos.le hrle 2
      dsimp [δ]
      nlinarith only [hsq]
    let k : ℕ := Nat.floor δ⁻¹
    refine ⟨k, ?_, ?_⟩
    · calc
        (k : ℝ) ≤ δ⁻¹ := Nat.floor_le (by positivity)
        _ = 9 * (A + 1) ^ 2 / ε ^ 2 := by
          dsimp [δ, r]
          field_simp [hεpos.ne', (show A + 1 ≠ 0 by positivity)]
          norm_num
    · calc
        ThresholdFunctions.fourierWeightAbove k f ≤
            3 * ThresholdFunctions.noiseSensitivity δ f :=
          ThresholdFunctions.fourierWeightAbove_le_three_mul_noiseSensitivity
            f hf hδpos hδle
        _ ≤ 3 * (A * Real.sqrt δ) :=
          mul_le_mul_of_nonneg_left
            (hPeres (f := f) ⟨hf, hltf⟩ δ ⟨hδpos, hδle⟩) (by norm_num)
        _ ≤ ε := by
          dsimp only [δ]
          rw [Real.sqrt_sq hrpos.le]
          have hrden : 3 * (A + 1) * r = ε := by
            dsimp [r]
            field_simp [(show A + 1 ≠ 0 by positivity)]
          nlinarith only [hrden, hrpos]
)

/-- For `B ≥ 1`, `0 < ε, η ≤ 1/2`, and `k ≤ B / ε²`, the optimized junta
prefactor `(ε (η/(2+η))^k)^(-(1+η))` is at most
`(1/η)^(200B/ε²)`. [OD14, Rmk. 9.29; Cor. 9.31, proof]
The constant `200` is a convenient explicit enlargement of the source bound.

**Proof sketch.** Bound the reciprocal power with exponent `1 + η` by its square,
then bound the squared reciprocal noise factor by `9/η²`. Apply the existing
polynomial absorption estimate with parameter `η²` and auxiliary influence
`B/ε`. Simplifying its resulting power gives the stated exponent. -/
lemma linearThreshold_junta_size_bound (B ε η : ℝ) (hB : 1 ≤ B)
    (hε : ε ∈ Set.Ioc 0 (1 / 2)) (hη : η ∈ Set.Ioc 0 (1 / 2))
    (k : ℕ) (hk : (k : ℝ) ≤ B / ε ^ 2) :
    1 / (ε * (η / (2 + η)) ^ k) ^ (1 + η) ≤
      (1 / η) ^ (200 * B / ε ^ 2) :=
  (by
    let ρ : ℝ := η / (2 + η)
    let I : ℝ := B / ε
    have hεpos : 0 < ε := hε.1
    have hηpos : 0 < η := hη.1
    have hBpos : 0 < B := by linarith only [hB]
    have hεone : ε ≤ 1 := by linarith only [hε.2]
    have hdenpos : 0 < 2 + η := by linarith only [hη.1]
    have hρpos : 0 < ρ := by dsimp [ρ]; positivity
    have hρle : ρ ≤ 1 := by
      dsimp [ρ]
      apply (div_le_iff₀ hdenpos).2
      linarith only [hη.1]
    have hIone : 1 ≤ I := by
      dsimp [I]
      apply (le_div_iff₀ hε.1).2
      linarith only [hB, hεone]
    have hquot : I / ε = B / ε ^ 2 := by
      dsimp [I]
      field_simp [ne_of_gt hε.1]
  
    have hsize :
        1 / (ε * ρ ^ k) ^ (1 + η) ≤
          4 * I ^ 3 / ε ^ 2 * (9 / η ^ 2) ^ k := by
      have hcpos : 0 < ε * ρ ^ k := by positivity
      have hcle : ε * ρ ^ k ≤ 1 := by
        calc
          ε * ρ ^ k ≤ ε * 1 :=
            mul_le_mul_of_nonneg_left
              (pow_le_one₀ hρpos.le hρle) hε.1.le
          _ ≤ 1 := by simpa using hεone
      have hrecip : 1 ≤ 1 / (ε * ρ ^ k) := by
        apply (le_div_iff₀ hcpos).2
        simpa using hcle
      have hρfactor : 1 / ρ ^ 2 ≤ 9 / η ^ 2 := by
        have hdenpow :=
          pow_le_pow_left₀ hdenpos.le
            (show 2 + η ≤ 3 by linarith only [hη.2]) 2
        norm_num at hdenpow
        calc
          1 / ρ ^ 2 = (2 + η) ^ 2 / η ^ 2 := by
            dsimp [ρ]
            field_simp [ne_of_gt hη.1, ne_of_gt hdenpos]
          _ ≤ 9 / η ^ 2 := by
            simpa only [div_eq_mul_inv] using
              (mul_le_mul_of_nonneg_right hdenpow
                (show 0 ≤ (η ^ 2)⁻¹ by positivity))
      have hcube : 1 ≤ I ^ 3 := by
        simpa using
          (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hIone 3)
      have hpref : 1 / ε ^ 2 ≤ 4 * I ^ 3 / ε ^ 2 := by
        have hnum : 1 ≤ 4 * I ^ 3 := by linarith only [hcube]
        simpa only [div_eq_mul_inv] using
          (mul_le_mul_of_nonneg_right hnum
            (show 0 ≤ (ε ^ 2)⁻¹ by positivity))
      calc
        1 / (ε * ρ ^ k) ^ (1 + η) =
            (1 / (ε * ρ ^ k)) ^ (1 + η) := by
          simp only [one_div, Real.inv_rpow hcpos.le]
        _ ≤ (1 / (ε * ρ ^ k)) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hrecip
            (by linarith only [hη.2])
        _ = 1 / ε ^ 2 * (1 / ρ ^ 2) ^ k := by
          rw [Real.rpow_two, one_div_pow, mul_pow,
            pow_right_comm ρ k 2, one_div_pow]
          field_simp [ne_of_gt hε.1, ne_of_gt hρpos]
        _ ≤ 1 / ε ^ 2 * (9 / η ^ 2) ^ k :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hρfactor k) (by positivity)
        _ ≤ 4 * I ^ 3 / ε ^ 2 * (9 / η ^ 2) ^ k :=
          mul_le_mul_of_nonneg_right hpref (by positivity)
  
    have hηsq : η ^ 2 ≤ 1 / 2 := by
      have hs := pow_le_pow_left₀ hη.1.le hη.2 2
      norm_num at hs
      linarith only [hs]
    have hcutoff : (k : ℝ) ≤ 3 * (I / ε) := by
      rw [hquot]
      have hnonneg : 0 ≤ B / ε ^ 2 := by positivity
      linarith only [hk, hnonneg]
    have habs :=
      ComparisonAux.junta_polynomial_absorption (η ^ 2) I ε
        (by positivity) hηsq hε.1 hεone (le_trans hεone hIone) k hcutoff
    have hexponent : (2 : ℝ) * (100 * I / ε) = 200 * B / ε ^ 2 := by
      calc
        2 * (100 * I / ε) = 200 * (I / ε) := by ring
        _ = 200 * (B / ε ^ 2) := by rw [hquot]
        _ = 200 * B / ε ^ 2 := by ring
    calc
      1 / (ε * (η / (2 + η)) ^ k) ^ (1 + η) ≤
          4 * I ^ 3 / ε ^ 2 * (9 / η ^ 2) ^ k := hsize
      _ ≤ (1 / η ^ 2) ^ (100 * I / ε) := habs
      _ = (1 / η) ^ (200 * B / ε ^ 2) := by
        rw [← one_div_pow]
        calc
          ((1 / η) ^ (2 : ℕ)) ^ (100 * I / ε) =
              (1 / η) ^ ((2 : ℝ) * (100 * I / ε)) := by
            simpa using
              (Real.rpow_natCast_mul (show 0 ≤ 1 / η by positivity)
                2 (100 * I / ε)).symm
          _ = (1 / η) ^ (200 * B / ε ^ 2) := by rw [hexponent]
)

/-- An LTF is `ε`-close to a junta on at most `I[f]^(2+η) (1/η)^(C/ε²)` coordinates
for an absolute `C` and `0 < ε,η ≤ 1/2`. [OD14, Cor. 9.31]

**Proof sketch.** Peres's theorem gives Fourier concentration at degree `O(1/ε²)`.
Use that cutoff in Remark 9.29's optimized junta bound and absorb the remaining factors
into the power of `1/η`. -/
theorem linearThreshold_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f → ThresholdFunctions.IsLinearThreshold f →
      ∀ ε η : ℝ, ε ∈ Set.Ioc 0 (1 / 2) → η ∈ Set.Ioc 0 (1 / 2) →
      ∃ (J : Finset (Fin n)) (h : BooleanFunc n),
        (J.card : ℝ) ≤ (totalInfluence f) ^ (2 + η) * (1 / η) ^ (C / ε ^ 2) ∧
        isPmOne h ∧ KKL.IsJunta h J ∧ ThresholdFunctions.IsClose f h ε := (by
    obtain ⟨B, hB, hcutoff⟩ := linearThreshold_fourier_cutoff
    refine ⟨200 * B, by linarith only [hB], ?_⟩
    intro n f hf hltf ε η hε hη
    have hεpos : 0 < ε := hε.1
    have hηpos : 0 < η := hη.1
    have hInonneg : 0 ≤ totalInfluence f := by
      rw [totalInfluence_eq_sum_sq_deg]
      exact Finset.sum_nonneg fun S _ => by positivity
    by_cases hIzero : totalInfluence f = 0
    · have hvariance :
          cubeVariance f = ThresholdFunctions.fourierWeightAbove 0 f := by
        rw [cubeVariance_eq_sum_nonempty_fourier]
        simp [ThresholdFunctions.fourierWeightAbove, Nat.pos_iff_ne_zero,
          Finset.card_eq_zero]
      have hvariance_le : cubeVariance f ≤ 0 := by
        rw [hvariance]
        simpa [hIzero] using
          (fourierWeightAbove_le_totalInfluence_div_succ f 0)
      obtain ⟨h, hh, hJ, herror⟩ := exists_boolean_constant_approximation f hf
      refine ⟨∅, h, ?_, hh, hJ, ?_⟩
      · rw [hIzero,
          Real.zero_rpow (show 2 + η ≠ 0 by linarith only [hηpos])]
        simp
      · change ThresholdFunctions.disagreementProbability f h ≤ ε
        linarith only [herror, hvariance_le, hεpos]
    · have hIpos : 0 < totalInfluence f :=
        lt_of_le_of_ne hInonneg (fun h => hIzero h.symm)
      obtain ⟨k, hk, htail⟩ := hcutoff n f hf hltf ε hε
      obtain ⟨J, h, hcard, hh, hJ, hclose⟩ :=
        optimized_junta_of_fourier_tail f hf hIpos ε η hεpos hηpos k htail
      refine ⟨J, h, ?_, hh, hJ, hclose⟩
      have hsize := linearThreshold_junta_size_bound B ε η hB hε hη k hk
      apply hcard.trans
      simpa only [div_eq_mul_inv, one_mul] using
        (mul_le_mul_of_nonneg_left hsize
          (show 0 ≤ (totalInfluence f) ^ (2 + η) by positivity))
)


end BooleanAnalysis.Hypercontractivity
