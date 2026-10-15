/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty, Mina Sha
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Concentration
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Rounding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier concentration and Friedgut's junta theorem

## Main definitions

No new definitions. Approximants are Boolean functions on the original cube.

## Main results

* `optimized_junta_of_fourier_tail`: Fourier concentration gives an optimized influence bound.
* `lowInfluence_fourierConcentration`: influential coordinates capture low-degree Fourier
  weight and give a Boolean junta approximation when the high-degree tail is small.
* `friedgut_junta`: every Boolean function is approximated by a junta with an exponential
  bound in its total influence divided by the error.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §9.6, Theorem 9.28 and Friedgut's Junta Theorem.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

/-- Coordinates of influence at least `ε² 9^(-k)/I[f]²` capture all but `ε` of the
degree-at-most-`k` Fourier weight and number at most `I[f]³ 9^k/ε²`. A tail bound of `ε`
then gives an `ε`-close Boolean junta on those coordinates. [OD14, Thm. 9.28]
For constants the threshold is set to one, making the coordinate set empty and resolving
the source's division by zero.

**Proof sketch.** Sum one-third-stable influences over omitted coordinates and use the
degree cutoff. Add the high-degree tail, then use the randomized-rounding argument of
Exercise 3.34 to obtain a Boolean approximant with half the spectral error. -/
theorem lowInfluence_fourierConcentration {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (ε : ℝ) (hε : ε ∈ Set.Ioc 0 1) (k : ℕ) :
    let τ := if totalInfluence f = 0 then 1
      else ε ^ 2 / (totalInfluence f) ^ 2 / (9 : ℝ) ^ k
    let J := KKL.influentialCoords f τ
    (J.card : ℝ) ≤ (totalInfluence f) ^ 3 / ε ^ 2 * (9 : ℝ) ^ k ∧
    (∑ S : Finset (Fin n),
      if S.card ≤ k ∧ ¬ (S ⊆ J) then fourierCoeff f S ^ 2 else 0) ≤ ε ∧
    (ThresholdFunctions.fourierWeightAbove k f ≤ ε →
      (∑ S : Finset (Fin n),
        if S ⊆ J ∧ S.card ≤ k then 0 else fourierCoeff f S ^ 2) ≤ 2 * ε ∧
      ∃ h : BooleanFunc n, isPmOne h ∧ KKL.IsJunta h J ∧ ThresholdFunctions.IsClose f h ε) :=
  (by
  classical
  dsimp only
  set T : ℝ := totalInfluence f with hTdef
  set τ : ℝ := if T = 0 then 1 else ε ^ 2 / T ^ 2 / (9 : ℝ) ^ k with hτdef
  set J : Finset (Fin n) := KKL.influentialCoords f τ with hJdef
  have hεpos : 0 < ε := hε.1
  have hTnonneg : 0 ≤ T := by
    rw [hTdef, totalInfluence_eq_sum_sq_deg]
    positivity
  have hτpos : 0 < τ := by
    rw [hτdef]
    split_ifs with h0
    · norm_num
    · have hTpos : 0 < T :=
        lt_of_le_of_ne hTnonneg (fun h => h0 h.symm)
      positivity
  have hcard : (J.card : ℝ) ≤ T ^ 3 / ε ^ 2 * (9 : ℝ) ^ k := by
    calc
      (J.card : ℝ) ≤ T / τ := KKL.influential_coords_card f τ hτpos
      _ = T ^ 3 / ε ^ 2 * (9 : ℝ) ^ k := by
        by_cases h0 : T = 0
        · simp [hτdef, h0]
        · rw [hτdef, if_neg h0]
          field_simp [h0, hεpos.ne']
  have hlowBound :
      (∑ S : Finset (Fin n),
        if S.card ≤ k ∧ ¬ S ⊆ J then fourierCoeff f S ^ 2 else 0) ≤ ε := by
    have hlow := fourier_omission_le f hf J k (1 / 3) τ
      (by norm_num) hτpos.le (by
        intro i hi
        have hout : ¬ τ ≤ influence i f := by
          simpa [J, KKL.influentialCoords] using hi
        exact le_of_not_ge hout)
    norm_num only at hlow
    rw [← Real.sqrt_eq_rpow, ← hTdef] at hlow
    have hscale : Real.sqrt τ * T ≤ (1 / 3 : ℝ) ^ k * ε := by
      by_cases h0 : T = 0
      · simp only [h0, mul_zero]
        positivity
      · have hTpos : 0 < T :=
          lt_of_le_of_ne hTnonneg (fun h => h0 h.symm)
        have hτsquare : τ = (ε / (T * (3 : ℝ) ^ k)) ^ 2 := by
          rw [hτdef, if_neg h0, div_pow, mul_pow,
            pow_right_comm (3 : ℝ) k 2]
          norm_num only
          field_simp [h0]
        rw [hτsquare, Real.sqrt_sq (by positivity), one_div_pow]
        apply le_of_eq
        field_simp [h0]
    have hrate : 0 < (1 / 3 : ℝ) ^ k := by positivity
    exact (mul_le_mul_iff_right₀ hrate).mp (hlow.trans hscale)
  refine ⟨hcard, hlowBound, ?_⟩
  intro htail
  have hdiscard :
      (∑ S : Finset (Fin n),
        if S ⊆ J ∧ S.card ≤ k then 0 else fourierCoeff f S ^ 2) ≤ 2 * ε := by
    calc
      (∑ S : Finset (Fin n),
          if S ⊆ J ∧ S.card ≤ k then 0 else fourierCoeff f S ^ 2) =
          (∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬ S ⊆ J then fourierCoeff f S ^ 2 else 0) +
          ThresholdFunctions.fourierWeightAbove k f := by
        unfold ThresholdFunctions.fourierWeightAbove
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hk : S.card ≤ k
        · have hnot : ¬ k < S.card := by omega
          by_cases hS : S ⊆ J <;> simp [hk, hS, hnot]
        · have hgt : k < S.card := by omega
          simp [hk, hgt]
      _ ≤ 2 * ε := by linarith only [hlowBound, htail]
  have houtside :
      (∑ S : Finset (Fin n), if S ⊆ J then 0 else fourierCoeff f S ^ 2) ≤
        ∑ S : Finset (Fin n),
          if S ⊆ J ∧ S.card ≤ k then 0 else fourierCoeff f S ^ 2 := by
    apply Finset.sum_le_sum
    intro S _
    by_cases hS : S ⊆ J
    · split_ifs <;> positivity
    · simp [hS]
  obtain ⟨h, hh, hjunta, herror⟩ := exists_boolean_junta_of_fourier_omission f hf J
  refine ⟨hdiscard, h, hh, hjunta, ?_⟩
  change ThresholdFunctions.disagreementProbability f h ≤ ε
  linarith only [herror, houtside, hdiscard]
)


/-- Every Boolean function is `ε`-close to a junta on at most `exp(C I[f]/ε)` coordinates
for an absolute `C`; the same set captures all but `2ε` of its Fourier weight at degrees
at most `I[f]/ε`. [OD14, §9.6, Friedgut's Junta Theorem]
The junta bound is independent of ambient dimension.

**Proof sketch.** Markov's inequality bounds the Fourier tail above the integer part
of `I[f]/ε`. Apply Theorem 9.28 at that cutoff. Writing its polynomial factor as
`ε (I[f]/ε)³`, use exponential growth to absorb it and the degree factor uniformly,
including zero total influence. -/
theorem friedgut_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f → ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
      ∃ (J : Finset (Fin n)) (h : BooleanFunc n),
        (J.card : ℝ) ≤ Real.exp (C * totalInfluence f / ε) ∧
        (∑ S : Finset (Fin n), if S ⊆ J ∧ (S.card : ℝ) ≤ totalInfluence f / ε
          then 0 else fourierCoeff f S ^ 2) ≤ 2 * ε ∧
        isPmOne h ∧ KKL.IsJunta h J ∧ ThresholdFunctions.IsClose f h ε := (by
  classical
  refine ⟨11, by norm_num, ?_⟩
  intro n f hf ε hε
  have hεpos : 0 < ε := hε.1
  set I : ℝ := totalInfluence f with hIdef
  have hInonneg : 0 ≤ I := by
    rw [hIdef, totalInfluence_eq_sum_sq_deg]
    positivity
  let t : ℝ := I / ε
  have ht : 0 ≤ t := by positivity
  let k : ℕ := ⌊t⌋₊
  have hkle : (k : ℝ) ≤ t := Nat.floor_le ht
  have hlt : t < (k : ℝ) + 1 := by
    simpa [k] using
      (Nat.lt_of_floor_lt (a := t) (Nat.lt_succ_self ⌊t⌋₊))
  have hdegree (S : Finset (Fin n)) :
      (S.card : ℝ) ≤ I / ε ↔ S.card ≤ k :=
    (Nat.le_floor_iff ht).symm
  have htail : ThresholdFunctions.fourierWeightAbove k f ≤ ε := by
    calc
      ThresholdFunctions.fourierWeightAbove k f ≤ I / ((k : ℝ) + 1) :=
        fourierWeightAbove_le_totalInfluence_div_succ f k
      _ ≤ ε := by
        apply (div_le_iff₀ (by positivity)).mpr
        linarith only [(div_lt_iff₀ hεpos).mp hlt]
  let J : Finset (Fin n) := KKL.influentialCoords f
    (if I = 0 then 1 else ε ^ 2 / I ^ 2 / (9 : ℝ) ^ k)
  obtain ⟨hcard, _, hconcentration⟩ :=
    lowInfluence_fourierConcentration f hf ε hε k
  obtain ⟨hspectral, h, hh, hjunta, hclose⟩ := hconcentration htail
  have hpolynomial : I ^ 3 / ε ^ 2 ≤ Real.exp (3 * t) := by
    calc
      I ^ 3 / ε ^ 2 = ε * t ^ 3 := by
        dsimp [t]
        field_simp [hεpos.ne']
      _ ≤ t ^ 3 := by
        simpa using mul_le_mul_of_nonneg_right hε.2
          (show 0 ≤ t ^ 3 by positivity)
      _ ≤ Real.exp t ^ 3 :=
        pow_le_pow_left₀ ht
          (by linarith only [Real.add_one_le_exp t]) 3
      _ = Real.exp (3 * t) := (Real.exp_nat_mul t 3).symm
  have hdegreeFactor : (9 : ℝ) ^ k ≤ Real.exp (8 * t) := by
    calc
      (9 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 9) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (8 * t) := by
        apply Real.exp_le_exp.mpr
        calc
          (k : ℝ) * Real.log 9 ≤ t * Real.log 9 :=
            mul_le_mul_of_nonneg_right hkle (Real.log_nonneg (by norm_num))
          _ ≤ t * 8 :=
            mul_le_mul_of_nonneg_left
              (by linarith only [Real.log_le_sub_one_of_pos (show 0 < (9 : ℝ) by norm_num)]) ht
          _ = 8 * t := by ring
  refine ⟨J, h, ?_, ?_, hh, hjunta, hclose⟩
  · change (J.card : ℝ) ≤ Real.exp (11 * I / ε)
    calc
      (J.card : ℝ) ≤ I ^ 3 / ε ^ 2 * (9 : ℝ) ^ k := hcard
      _ ≤ Real.exp (3 * t) * (9 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hpolynomial (by positivity)
      _ ≤ Real.exp (3 * t) * Real.exp (8 * t) :=
        mul_le_mul_of_nonneg_left hdegreeFactor (by positivity)
      _ = Real.exp (11 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (11 * I / ε) := by
        congr 1
        dsimp [t]
        ring
  · change (∑ S : Finset (Fin n),
      if S ⊆ J ∧ (S.card : ℝ) ≤ I / ε then 0 else fourierCoeff f S ^ 2) ≤ 2 * ε
    simpa only [hdegree] using hspectral
)

/-- If a ±1-valued cube function has positive total influence `I[f]` and Fourier
weight at most `ε > 0` above degree `k`, then for every `η > 0` it has an
`ε`-close Boolean junta on at most
`I[f]^(2+η) / (ε ρ^k)^(1+η)` coordinates, where `ρ = η/(2+η)`.
[OD14, Rmk. 9.29; Ex. 9.31]
This formulation retains the exact noise parameter and requires only positivity
of `ε` and `η`.

**Proof sketch.** Choose a positive influence threshold through logarithms so that
its power `1/(1+η)`, multiplied by total influence, equals `ε ρ^k`.
At noise rate `ρ`, the weighted omission estimate bounds the omitted low-degree
Fourier weight by `ε`. Adding the assumed tail bounds all omitted weight by
`2ε`, so Boolean junta rounding gives disagreement at most `ε`. The number of
coordinates above the threshold is at most total influence divided by the
threshold, which simplifies to the stated bound. -/
lemma optimized_junta_of_fourier_tail {n : ℕ} (f : BooleanFunc n)
    (hf : isPmOne f) (hI : 0 < totalInfluence f)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (k : ℕ)
    (htail : ThresholdFunctions.fourierWeightAbove k f ≤ ε) :
    let ρ := η / (2 + η)
    ∃ (J : Finset (Fin n)) (h : BooleanFunc n),
      (J.card : ℝ) ≤
        (totalInfluence f) ^ (2 + η) / (ε * ρ ^ k) ^ (1 + η) ∧
      isPmOne h ∧ KKL.IsJunta h J ∧ ThresholdFunctions.IsClose f h ε :=
  (by
  classical
  dsimp only
  set ρ : ℝ := η / (2 + η)
  let I : ℝ := totalInfluence f
  have hIpos : 0 < I := hI
  have hden : 0 < 2 + η := by linarith only [hη]
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρle : ρ ≤ 1 := by
    dsimp [ρ]
    apply (div_le_iff₀ hden).mpr
    linarith only [hη]
  let p : ℝ := 1 + η
  let a : ℝ := (1 - ρ) / (1 + ρ)
  let c : ℝ := ε * ρ ^ k
  have hc : 0 < c := by
    dsimp [c]
    positivity
  let b : ℝ := Real.log c - Real.log I
  let τ : ℝ := Real.exp (p * b)
  let J : Finset (Fin n) := KKL.influentialCoords f τ
  have hτpos : 0 < τ := Real.exp_pos _
  -- The exponential threshold gives exactly the desired omission budget and size.
  have hpa : p * a = 1 := by
    have hp : 0 < 1 + η := by linarith only [hη]
    dsimp [p, a, ρ]
    field_simp [hden.ne', hp.ne',
      (show (2 : ℝ) + 2 * η ≠ 0 by positivity)] <;> ring
  have hgain : τ ^ a * I = c := by
    have hpower : τ ^ a = Real.exp b := by
      rw [Real.rpow_def_of_pos hτpos]
      dsimp only [τ]
      rw [Real.log_exp]
      congr 1
      calc
        p * b * a = b * (p * a) := by ring
        _ = b := by rw [hpa]; ring
    calc
      τ ^ a * I = Real.exp b * Real.exp (Real.log I) := by
        rw [hpower, Real.exp_log hIpos]
      _ = Real.exp (b + Real.log I) := (Real.exp_add _ _).symm
      _ = c := by simp [b, Real.exp_log hc]
  have hcardValue : I / τ = I ^ (2 + η) / c ^ (1 + η) := by
    rw [Real.rpow_def_of_pos hIpos, Real.rpow_def_of_pos hc]
    change I / Real.exp (p * b) =
      Real.exp (Real.log I * (2 + η)) / Real.exp (Real.log c * p)
    rw [div_eq_mul_inv, div_eq_mul_inv,
      ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_log hIpos,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [b, p]
    simp only [Real.log_exp]
    ring
  -- Apply the weighted omission estimate at the optimized noise rate.
  have hlow :
      (∑ S : Finset (Fin n),
        if S.card ≤ k ∧ ¬ S ⊆ J then fourierCoeff f S ^ 2 else 0) ≤ ε := by
    have homit := fourier_omission_le f hf J k ρ τ
      ⟨hρpos.le, hρle⟩ hτpos.le (by
        intro i hi
        apply le_of_not_ge
        simpa [J, KKL.influentialCoords] using hi)
    change ρ ^ k * _ ≤ τ ^ a * I at homit
    rw [hgain] at homit
    exact (mul_le_mul_iff_right₀ (show 0 < ρ ^ k by positivity)).mp
      (by simpa only [c, mul_comm] using homit)
  have hfull :
      (∑ S : Finset (Fin n),
        if S ⊆ J then 0 else fourierCoeff f S ^ 2) ≤ 2 * ε := by
    calc
      (∑ S : Finset (Fin n),
          if S ⊆ J then 0 else fourierCoeff f S ^ 2) ≤
          (∑ S : Finset (Fin n),
            if S.card ≤ k ∧ ¬ S ⊆ J then fourierCoeff f S ^ 2 else 0) +
          ThresholdFunctions.fourierWeightAbove k f := by
        unfold ThresholdFunctions.fourierWeightAbove
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro S _
        by_cases hS : S ⊆ J
        · rw [if_pos hS]
          split_ifs <;> positivity
        · by_cases hk : S.card ≤ k
          · have hnot : ¬ k < S.card := by omega
            simp [hS, hk, hnot]
          · have hgt : k < S.card := by omega
            simp [hS, hk, hgt]
      _ ≤ 2 * ε := by linarith only [hlow, htail]
  obtain ⟨h, hh, hjunta, herror⟩ := exists_boolean_junta_of_fourier_omission f hf J
  refine ⟨J, h, ?_, hh, hjunta, ?_⟩
  · calc
      (J.card : ℝ) ≤ I / τ := KKL.influential_coords_card f τ hτpos
      _ = I ^ (2 + η) / c ^ (1 + η) := hcardValue
  · change ThresholdFunctions.disagreementProbability f h ≤ ε
    linarith only [herror, hfull]
)

end BooleanAnalysis.Hypercontractivity
