/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty, Mina Sha
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Definitions
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Elementary
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Concentration
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Rounding
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Junta
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.DNF
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.KKL.Threshold
import TCSlib.BooleanAnalysis.Hypercontractivity.Applications.Influence
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Norms
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Comparison
import TCSlib.BooleanAnalysis.Switching

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Full KKL and exponential junta statements

## Main definitions

No new definitions. Boolean approximants on the original cube depend only on a small set
of coordinates, implementing the cylinder extension of a junta.

## Main results

* `kkl`, `kkl_edgeIsoperimetric`: full variance-scaled KKL and its explicit stronger bound.
* `lowInfluence_fourierConcentration`: Theorem 9.28, with its approximation consequence.
* `friedgut_junta`: the dimension-independent exponential junta theorem.
* `dnf_junta`, `linearThreshold_junta`, `exists_large_nonempty_fourierCoeff`: 9.30–9.32.

This module combines the cube KKL development and its hypercontractive consequences.
The supporting `KKL.Basic` and `KKL.Elementary` modules contain definitions and
elementary estimates, respectively.
Every hidden asymptotic constant is quantified before the dimension, function, and accuracy.

## Contents

* `KKL.Basic`: Fourier definitions and finite-dimensional approximation.
* `KKL.Elementary`: averaging, elementary influence bounds and junta estimates.
* `KKL.Concentration`: bounds for Fourier weight involving omitted coordinates.
* `KKL.Rounding`: coordinate averaging and Boolean junta approximation.
* `KKL.Junta`: low-influence Fourier concentration and Friedgut's theorem.
* `KKL.DNF`: Fourier tails, influence bounds and juntas for bounded-width DNFs.
* `KKL.Threshold`: junta approximation of linear threshold functions.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §9.6, Theorem 9.28, Friedgut's Junta Theorem, Corollaries 9.30–9.32.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

/-- A nonconstant Boolean function has maximum influence at least `(9/Ĩ²) 9^(-Ĩ)`,
where `Ĩ=I[f]/Var[f]`. [OD14, §9.6, KKL Edge-Isoperimetric Theorem]

**Proof sketch.** Normalize the nonempty Fourier weights to a distribution and apply
Jensen to `3^(-|S|)`. Bound the stable influence sum using Corollary 9.12 and the square
root of maximum influence, then square and rearrange. -/
theorem kkl_edgeIsoperimetric {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (hvar : 0 < cubeVariance f) :
    let I := totalInfluence f / cubeVariance f
    (9 / I ^ 2) * (9 : ℝ) ^ (-I) ≤ ThresholdFunctions.maxInfluence f := (by
  classical
  let I : ℝ := totalInfluence f / cubeVariance f
  change (9 / I ^ 2) * (9 : ℝ) ^ (-I) ≤ ThresholdFunctions.maxInfluence f
  have hT : 0 < totalInfluence f := by
    apply hvar.trans_le
    simpa only [Real.one_rpow, one_pow, mul_one,
      ← totalInfluence_eq_sum_sq_deg] using
      cubeVariance_rpow_ratio_le_noisy_total f hvar 1 zero_lt_one
  have hstable :
      3 * cubeVariance f * (1 / 3 : ℝ) ^ I ≤
        ∑ i : Fin n, influence i f ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ 3 * ∑ S : Finset (Fin n),
          (S.card : ℝ) * (1 / 3 : ℝ) ^ S.card * fourierCoeff f S ^ 2 := by
        simpa only [I, mul_assoc] using
          mul_le_mul_of_nonneg_left
            (cubeVariance_rpow_ratio_le_noisy_total f hvar (1 / 3) (by norm_num))
            (by norm_num : (0 : ℝ) ≤ 3)
      _ = ∑ i : Fin n, KKL.noisyInfluence (1 / 3) i f := by
        rw [KKL.sum_noisyInfluence, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        cases S.card with
        | zero => simp
        | succ k =>
          simp only [Nat.succ_sub_one, pow_succ]
          ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => stableInfluence_one_third f hf i
  have hpow : ((1 / 3 : ℝ) ^ I) ^ 2 = (9 : ℝ) ^ (-I) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by norm_num : 0 ≤ (1 / 3 : ℝ)),
      mul_comm I (2 : ℝ),
      Real.rpow_mul (by norm_num : 0 ≤ (1 / 3 : ℝ)), Real.rpow_two]
    norm_num [Real.rpow_neg_eq_inv_rpow]
  obtain ⟨i, hi⟩ := FiniteNorms.exists_sq_div_sum_le_of_sum_three_halves
    (fun i : Fin n => influence i f)
    (fun i => by
      unfold influence
      exact ThresholdFunctions.expect_nonneg
        (fun x => div_nonneg (sq_nonneg _) (by norm_num)))
    hT (3 * cubeVariance f * (1 / 3 : ℝ) ^ I) (by positivity) hstable
  calc
    _ = ((3 * cubeVariance f * (1 / 3 : ℝ) ^ I) / totalInfluence f) ^ 2 := by
      simp only [div_pow, mul_pow, hpow]
      dsimp [I]
      field_simp [hT.ne', hvar.ne']
      ring
    _ ≤ influence i f := hi
    _ ≤ |influence i f| := le_abs_self _
    _ ≤ ThresholdFunctions.maxInfluence f :=
      le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
)

/-- In dimension at least two, every function taking values in `{-1,1}` has a coordinate
whose influence is at least `Var[f] ln(n)/(30n)`, including constant functions.
[OD14, §9.6, KKL Theorem]
This formulation uses the explicit natural-logarithm constant `1/30`.

**Proof sketch.** Choose a coordinate of maximal influence. Zero variance gives the bound
immediately. For positive variance, split according to the scalar dichotomy: large
normalized total influence gives the bound by averaging; otherwise use the exponential
edge-isoperimetric bound. Boolean variance is at most one, giving the required scaling
in the second case. -/
lemma exists_influence_ge_kkl_bound {n : ℕ} (f : BooleanFunc n) (hf : isPmOne f)
    (hn : 2 ≤ n) :
    ∃ i : Fin n,
      cubeVariance f * (Real.log (n : ℝ) / (30 * (n : ℝ))) ≤ influence i f :=
  (by
  classical
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hInf (j : Fin n) : 0 ≤ influence j f := by
    unfold influence
    exact ThresholdFunctions.expect_nonneg
      (fun x => div_nonneg (sq_nonneg _) (by norm_num))
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin n)) (fun j => influence j f) Finset.univ_nonempty
  have hsup : ThresholdFunctions.maxInfluence f ≤ influence i f := by
    unfold ThresholdFunctions.maxInfluence
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨j, rfl⟩
    change |influence j f| ≤ influence i f
    rw [abs_of_nonneg (hInf j)]
    exact hmax j (Finset.mem_univ j)
  refine ⟨i, ?_⟩
  by_cases hvar : 0 < cubeVariance f
  · let t : ℝ := totalInfluence f / cubeVariance f
    have hVT : cubeVariance f ≤ totalInfluence f := by
      simpa only [Real.one_rpow, one_pow, mul_one,
        ← totalInfluence_eq_sum_sq_deg] using
        cubeVariance_rpow_ratio_le_noisy_total f hvar 1 zero_lt_one
    have ht : 0 < t := div_pos (hvar.trans_le hVT) hvar
    have hcase := ComparisonAux.kkl_scalar_dichotomy
      (3 / 10) (Real.log 9) (Real.log (n : ℝ)) t
      (by norm_num)
      (by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
        nlinarith)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) ht
    rw [Real.exp_log hnR] at hcase
    norm_num only [show 100 * (3 / 10 : ℝ) = 30 by norm_num] at hcase
    rcases hcase with havg | hedge
    · obtain ⟨j, hj⟩ := max_influence_lower_bound f hn0
      calc
        _ ≤ cubeVariance f * (t / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left havg hvar.le
        _ = totalInfluence f / (n : ℝ) := by
          dsimp [t]
          field_simp [hvar.ne', hnR.ne']
        _ ≤ influence j f := hj
        _ ≤ influence i f := hmax j (Finset.mem_univ j)
    · have hV1 : cubeVariance f ≤ 1 := by
        rw [cubeVariance_eq_sum_nonempty_fourier, ← parseval_pm_one f hf]
        apply Finset.sum_le_sum
        intro S _
        split_ifs
        · exact sq_nonneg _
        · exact le_rfl
      have hEdge :
          (9 / t ^ 2) * (9 : ℝ) ^ (-t) ≤ influence i f :=
        (kkl_edgeIsoperimetric f hf hvar).trans hsup
      calc
        _ ≤ cubeVariance f * (t⁻¹ ^ 2 * Real.exp (-Real.log 9 * t)) :=
          mul_le_mul_of_nonneg_left hedge hvar.le
        _ ≤ 1 * (t⁻¹ ^ 2 * Real.exp (-Real.log 9 * t)) :=
          mul_le_mul_of_nonneg_right hV1 (by positivity)
        _ ≤ (9 / t ^ 2) * (9 : ℝ) ^ (-t) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 9)]
          simp only [one_mul, mul_neg, neg_mul, inv_pow]
          apply mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          calc
            (t ^ 2)⁻¹ = 1 / t ^ 2 := (one_div _).symm
            _ ≤ 9 / t ^ 2 :=
              div_le_div_of_nonneg_right (by norm_num) (sq_nonneg t)
        _ ≤ influence i f := hEdge
  · have hV0 : cubeVariance f = 0 := le_antisymm
      (le_of_not_gt hvar)
      (ThresholdFunctions.expect_nonneg (fun x => sq_nonneg _))
    simpa only [hV0, zero_mul] using hInf i
)

/-- A universal positive constant bounds maximum influence below by
`c Var[f] ln(n)/n` for every Boolean cube function. [OD14, §9.6, KKL Theorem]
Changing binary to natural logarithms is absorbed into the constant. The reused maximum
uses absolute influences, equal to influences by nonnegativity; dimension zero is harmless.

**Proof sketch.** If normalized total influence is at least a small multiple of `ln(n)`,
average the influences. Otherwise use the exponential edge-isoperimetric bound. -/
theorem kkl : ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f →
    c * cubeVariance f * (Real.log (n : ℝ) / (n : ℝ)) ≤
      ThresholdFunctions.maxInfluence f := (by
  classical
  refine ⟨1 / 30, by norm_num, ?_⟩
  intro n f hf
  by_cases hn : 2 ≤ n
  · obtain ⟨i, hi⟩ := exists_influence_ge_kkl_bound f hf hn
    calc
      _ = cubeVariance f * (Real.log (n : ℝ) / (30 * (n : ℝ))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ influence i f := hi
      _ ≤ |influence i f| := le_abs_self _
      _ ≤ ThresholdFunctions.maxInfluence f :=
        le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
  · have hn1 : n ≤ 1 := by omega
    interval_cases n
    · simp [ThresholdFunctions.maxInfluence, Set.range_eq_empty]
    · have hs : |influence (0 : Fin 1) f| ≤ ThresholdFunctions.maxInfluence f :=
        le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self (0 : Fin 1))
      simpa only [Nat.cast_one, Real.log_one, zero_div, mul_zero] using
        (abs_nonneg (influence (0 : Fin 1) f)).trans hs
)

/-- A Boolean function with variance at least one half has a nonempty Fourier coefficient
on at most `C I[f]` coordinates whose square is at least `exp(-C I[f]²)`.
[OD14, Cor. 9.32] A single absolute constant covers both asymptotic terms.

**Proof sketch.** Apply Friedgut's theorem with error `1/8`. At least a quarter of the
Fourier weight lies on nonempty retained sets. Count them and apply the pigeonhole principle. -/
theorem exists_large_nonempty_fourierCoeff : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : BooleanFunc n), isPmOne f → (1 / 2 : ℝ) ≤ cubeVariance f →
      ∃ S : Finset (Fin n), S.Nonempty ∧ (S.card : ℝ) ≤ C * totalInfluence f ∧
        Real.exp (-C * (totalInfluence f) ^ 2) ≤ fourierCoeff f S ^ 2 := (by
  classical
  obtain ⟨A, hA, hFriedgut⟩ := friedgut_junta
  refine ⟨64 * A + 32, by positivity, ?_⟩
  intro n f hf hvar
  set I : ℝ := totalInfluence f with hIdef
  have hI : (1 / 2 : ℝ) ≤ I := by
    have hJensen := cubeVariance_rpow_ratio_le_noisy_total f
      (by linarith only [hvar]) 1 (by norm_num)
    norm_num at hJensen
    rw [← totalInfluence_eq_sum_sq_deg] at hJensen
    exact hvar.trans hJensen
  have hIpos : 0 < I := by linarith only [hI]
  obtain ⟨J, _, hcard, hdiscard, _, _, _⟩ :=
    hFriedgut n f hf (1 / 8) (by constructor <;> norm_num)
  have hcut : totalInfluence f / (1 / 8 : ℝ) = 8 * I := by
    rw [← hIdef]
    ring
  rw [hcut] at hdiscard
  norm_num at hdiscard
  have hcardBound : (J.card : ℝ) ≤ Real.exp (8 * A * I) := by
    convert hcard using 1
    congr 1
    rw [← hIdef]
    ring
  let k : ℕ := ⌊8 * I⌋₊
  let F : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun S =>
      S ≠ ∅ ∧ S ⊆ J ∧ (S.card : ℝ) ≤ 8 * I)
  -- Retained nonempty Fourier weight is at least one quarter.
  have hmass : (1 / 4 : ℝ) ≤ ∑ S ∈ F, fourierCoeff f S ^ 2 := by
    have hcover : cubeVariance f ≤
        (∑ S ∈ F, fourierCoeff f S ^ 2) +
        ∑ S : Finset (Fin n),
          if S ⊆ J ∧ (S.card : ℝ) ≤ 8 * I then 0 else fourierCoeff f S ^ 2 := by
      rw [cubeVariance_eq_sum_nonempty_fourier]
      dsimp only [F]
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro S _
      by_cases hz : S = ∅
      · rw [if_pos hz]
        split_ifs <;> positivity
      · by_cases hret : S ⊆ J ∧ (S.card : ℝ) ≤ 8 * I <;> simp [hz, hret]
    linarith only [hvar, hcover, hdiscard]
  -- Count the retained family using its degree cutoff.
  have hbase : (J.card : ℝ) + 1 ≤ Real.exp ((8 * A + 2) * I) := by
    have hone : 1 ≤ Real.exp (8 * A * I) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have htwo : 2 ≤ Real.exp (2 * I) := by
      linarith only [hI, Real.add_one_le_exp (2 * I)]
    calc
      (J.card : ℝ) + 1 ≤ Real.exp (8 * A * I) + 1 := by
        linarith only [hcardBound]
      _ ≤ Real.exp (8 * A * I) * Real.exp (2 * I) := by
        nlinarith only [hone,
          mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg (8 * A * I))]
      _ = Real.exp ((8 * A + 2) * I) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hcountNat : F.card ≤ (J.card + 1) ^ k := by
    calc
      F.card ≤ (J.powerset.filter (fun S => S.card ≤ k)).card := by
        apply Finset.card_le_card
        intro S hS
        obtain ⟨_, hSJ, hSk⟩ := (Finset.mem_filter.mp hS).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSJ, ?_⟩
        exact (Nat.le_floor_iff (show 0 ≤ 8 * I by positivity)).mpr hSk
      _ ≤ (J.card + 1) ^ k := KKL.card_bounded_subsets_le J k
  have hfamilyCard : (F.card : ℝ) ≤ Real.exp ((64 * A + 16) * I ^ 2) := by
    have hcount : (F.card : ℝ) ≤ ((J.card : ℝ) + 1) ^ k := by
      exact_mod_cast hcountNat
    have hk : (k : ℝ) ≤ 8 * I := Nat.floor_le (by positivity)
    calc
      (F.card : ℝ) ≤ ((J.card : ℝ) + 1) ^ k := hcount
      _ ≤ Real.exp ((8 * A + 2) * I) ^ k :=
        pow_le_pow_left₀ (by positivity) hbase k
      _ = Real.exp ((k : ℝ) * ((8 * A + 2) * I)) :=
        (Real.exp_nat_mul _ k).symm
      _ ≤ Real.exp ((64 * A + 16) * I ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_right hk
          (show 0 ≤ (8 * A + 2) * I by positivity)]
  -- The proposed coefficient threshold has total mass at most one quarter.
  have hpigeon :
      (∑ _S ∈ F, Real.exp (-(64 * A + 32) * I ^ 2)) ≤
        ∑ S ∈ F, fourierCoeff f S ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc
      (F.card : ℝ) * Real.exp (-(64 * A + 32) * I ^ 2) ≤
          Real.exp ((64 * A + 16) * I ^ 2) *
            Real.exp (-(64 * A + 32) * I ^ 2) :=
        mul_le_mul_of_nonneg_right hfamilyCard (Real.exp_nonneg _)
      _ = Real.exp (-16 * I ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ 1 / 4 := by
        have hfour : 4 ≤ Real.exp (16 * I ^ 2) := by
          nlinarith only [Real.add_one_le_exp (16 * I ^ 2), hI,
            sq_nonneg (I - 1 / 2)]
        rw [show -16 * I ^ 2 = -(16 * I ^ 2) by ring, Real.exp_neg]
        have hreciprocal := one_div_le_one_div_of_le
          (show 0 < (4 : ℝ) by norm_num) hfour
        simpa only [one_div] using hreciprocal
      _ ≤ ∑ S ∈ F, fourierCoeff f S ^ 2 := hmass
  have hFnonempty : F.Nonempty := by
    by_contra hF
    have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    norm_num [hz] at hmass
  obtain ⟨S, hSF, hcoefficient⟩ :=
    Finset.exists_le_of_sum_le hFnonempty hpigeon
  obtain ⟨hSne, _, hScard⟩ := (Finset.mem_filter.mp hSF).2
  refine ⟨S, Finset.nonempty_iff_ne_empty.mpr hSne, ?_, hcoefficient⟩
  change (S.card : ℝ) ≤ (64 * A + 32) * I
  calc
    (S.card : ℝ) ≤ 8 * I := hScard
    _ ≤ (64 * A + 32) * I :=
      mul_le_mul_of_nonneg_right (by linarith only [hA]) hIpos.le
)


end BooleanAnalysis.Hypercontractivity

open BooleanAnalysis

namespace KKL

variable {n : ℕ}

/-- Every balanced Boolean cube function in dimension at least two has a coordinate
of influence at least `ln(n)/(30n)`. [OD14, §9.6, KKL Theorem]
This explicit natural-logarithm formulation preserves the older KKL API.

**Proof sketch.** Balance and the Boolean range make the variance one. Specialize
the quantitative variance-scaled KKL bound to this identity. -/
theorem KKL_balanced (f : BooleanFunc n) (hf : isPmOne f)
    (hbal : expect f = 0) (hn : 2 ≤ n) :
    ∃ i : Fin n, influence i f ≥ Real.log n / (30 * n) := (by
  have hvar : Hypercontractivity.cubeVariance f = 1 := by
    simpa only [Hypercontractivity.cubeVariance, hbal, sub_zero] using
      expect_sq_pm_one f hf
  simpa only [hvar, one_mul] using
    Hypercontractivity.exists_influence_ge_kkl_bound f hf hn
)

end KKL
