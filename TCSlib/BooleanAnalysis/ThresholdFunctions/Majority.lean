import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier coefficients of majority

This file states the exact and asymptotic formulas for the Fourier spectrum of the odd-arity
majority function.

## Main definitions

* `majorityLimitWeight`: the limiting Fourier weight on a fixed level.

## Main results

* `majority_fourierCoeff_even` and `majority_fourierCoeff_odd` give the exact coefficients.
* `majority_fourierCoeff_duality` relates complementary odd levels.
* `majority_weight_strictAnti`: each fixed odd level decreases with dimension.
* `majority_noiseStability_antitone`: at nonnegative correlation the noise stability of majority
  decreases with dimension.
* `majority_weight_tendsto` identifies the limiting level weights.
* `majority_weight_asymptotics` records the fixed-level and tail asymptotics.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, §5.3.
* [Tit62] R. C. Titsworth, Correlation properties of cyclic sequences, 1962.
* [Kal02] G. Kalai, A Fourier-theoretic perspective on the Condorcet paradox, 2002.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

/-! ## Limiting level weights -/

/-- The coefficient of `ρᵏ` in `(2/π) * arcsin ρ`, equivalently the limiting level-`k`
Fourier weight of majority. It is zero on even levels.

[OD14, Eq. (5.10)] -/
noncomputable def majorityLimitWeight (k : ℕ) : ℝ :=
  if Odd k then
    4 / (Real.pi * k * 2 ^ k) * Nat.choose (k - 1) ((k - 1) / 2)
  else 0

/-! ## Elementary properties of majority -/

/-- Majority is `±1`-valued. -/
lemma majority_isPmOne (m : ℕ) : isPmOne (majority m) := by
  intro x
  by_cases h : (Finset.univ.filter fun i ↦ x i = false).card > m
  · exact Or.inl (by simp [majority, h])
  · exact Or.inr (by simp [majority, h])

/-- Majority of odd arity is an odd function: negating every input bit negates the output. -/
lemma majority_isOddFunc (m : ℕ) : isOddFunc (majority m) := by
  classical
  intro x
  have hcompl : (Finset.univ.filter fun i : Fin (2 * m + 1) ↦ (!x i) = false).card
      = 2 * m + 1 - (Finset.univ.filter fun i : Fin (2 * m + 1) ↦ x i = false).card := by
    have hsplit : (Finset.univ.filter fun i : Fin (2 * m + 1) ↦ (!x i) = false)
        = Finset.univ \ Finset.univ.filter fun i : Fin (2 * m + 1) ↦ x i = false := by
      ext i
      simp
    rw [hsplit, Finset.card_sdiff]
    simp
  have hle : (Finset.univ.filter fun i : Fin (2 * m + 1) ↦ x i = false).card ≤ 2 * m + 1 := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin (2 * m + 1)))
      (fun i ↦ x i = false)
    simpa using h
  simp only [majority, hcompl]
  by_cases h : (Finset.univ.filter fun i : Fin (2 * m + 1) ↦ x i = false).card > m
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]
    norm_num

/-! ## Level weights and noise stability -/

/-- Fourier level weights are nonnegative. -/
lemma weightLevel_nonneg {n : ℕ} (k : ℕ) (f : BooleanFunc n) : 0 ≤ weightLevel k f := by
  refine Finset.sum_nonneg fun S _ ↦ ?_
  split
  · positivity
  · exact le_rfl

/-- There is no Fourier weight above the number of variables. -/
lemma weightLevel_eq_zero_of_lt {n k : ℕ} (hk : n < k) (f : BooleanFunc n) :
    weightLevel k f = 0 := by
  refine Finset.sum_eq_zero fun S _ ↦ ?_
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  exact if_neg (by omega)

/-- Grouping the Fourier expansion by levels: any weighting depending only on the cardinality of a
set can be summed level by level. -/
lemma sum_fourier_sq_eq_sum_weightLevel {n : ℕ} (g : ℕ → ℝ) (f : BooleanFunc n) :
    ∑ S : Finset (Fin n), g S.card * fourierCoeff f S ^ 2
      = ∑ k ∈ Finset.range (n + 1), g k * weightLevel k f := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (n + 1))
      (g := fun S : Finset (Fin n) ↦ S.card)
      (fun S _ ↦ by
        have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
        simp only [Finset.mem_range]
        omega)
      (fun S ↦ g S.card * fourierCoeff f S ^ 2)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [weightLevel, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  by_cases hS : S.card = k <;> simp [hS]

/-- Noise stability as the generating function of the Fourier level weights. -/
lemma noiseStability_eq_sum_weightLevel {n : ℕ} (ρ : ℝ) (f : BooleanFunc n) :
    noiseStability ρ f = ∑ k ∈ Finset.range (n + 1), ρ ^ k * weightLevel k f := by
  rw [noiseStability, stability_formula]
  exact sum_fourier_sq_eq_sum_weightLevel (fun k ↦ ρ ^ k) f

/-- Parseval, level by level. -/
lemma sum_weightLevel_eq_one {n : ℕ} {f : BooleanFunc n} (hf : isPmOne f) :
    ∑ k ∈ Finset.range (n + 1), weightLevel k f = 1 := by
  have h := sum_fourier_sq_eq_sum_weightLevel (fun _ ↦ (1 : ℝ)) f
  simp only [one_mul] at h
  rw [← h, parseval_pm_one f hf]

/-- Summation by parts: if the partial sums of `b` never exceed those of `a`, the two sequences
have the same total mass, and the weights `ρ ^ k` are nonincreasing, then `b` has the smaller
generating-function value. -/
lemma sum_pow_mul_le_of_prefix_le {N : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (a b : ℕ → ℝ)
    (hpre : ∀ j, j ≤ N → ∑ k ∈ Finset.range j, b k ≤ ∑ k ∈ Finset.range j, a k)
    (htot : ∑ k ∈ Finset.range N, b k = ∑ k ∈ Finset.range N, a k) :
    ∑ k ∈ Finset.range N, ρ ^ k * b k ≤ ∑ k ∈ Finset.range N, ρ ^ k * a k := by
  set d : ℕ → ℝ := fun k ↦ a k - b k with hd
  have hsum : ∑ k ∈ Finset.range N, ρ ^ k * a k - ∑ k ∈ Finset.range N, ρ ^ k * b k
      = ∑ k ∈ Finset.range N, ρ ^ k * d k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hd]; ring
  have hD : ∀ j, j ≤ N → 0 ≤ ∑ k ∈ Finset.range j, d k := by
    intro j hj
    have h := hpre j hj
    have hrw : ∑ k ∈ Finset.range j, d k
        = ∑ k ∈ Finset.range j, a k - ∑ k ∈ Finset.range j, b k := by
      rw [← Finset.sum_sub_distrib]
    rw [hrw]
    linarith
  have hDN : ∑ k ∈ Finset.range N, d k = 0 := by
    have hrw : ∑ k ∈ Finset.range N, d k
        = ∑ k ∈ Finset.range N, a k - ∑ k ∈ Finset.range N, b k := by
      rw [← Finset.sum_sub_distrib]
    rw [hrw, htot]
    ring
  have key : ∑ k ∈ Finset.range N, ρ ^ k * d k
      = ∑ i ∈ Finset.range (N - 1), (ρ ^ i - ρ ^ (i + 1)) * ∑ k ∈ Finset.range (i + 1), d k := by
    have h := Finset.sum_range_by_parts (fun k : ℕ ↦ ρ ^ k) d N
    simp only [smul_eq_mul] at h
    rw [h, hDN, mul_zero, zero_sub, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hnonneg : 0 ≤ ∑ i ∈ Finset.range (N - 1),
      (ρ ^ i - ρ ^ (i + 1)) * ∑ k ∈ Finset.range (i + 1), d k := by
    refine Finset.sum_nonneg fun i hi ↦ ?_
    have hi' : i + 1 ≤ N := by
      rw [Finset.mem_range] at hi
      omega
    have h1 : ρ ^ (i + 1) ≤ ρ ^ i := by
      rw [pow_succ]
      nlinarith [pow_nonneg hρ0 i]
    exact mul_nonneg (by linarith) (hD (i + 1) hi')
  linarith [hsum, key ▸ hnonneg]

/-! ## Exact Fourier coefficients -/

/-- Every even-degree Fourier coefficient of odd-arity majority vanishes.
[OD14, Thm. 5.19]

**Proof sketch.** Majority is odd under simultaneous negation of all input bits. Pairing each input
with its negation shows that an even Walsh character has zero correlation with majority. -/
theorem majority_fourierCoeff_even (m : ℕ) (S : Finset (Fin (2 * m + 1)))
    (hS : Even S.card) :
    fourierCoeff (majority m) S = 0 :=
  fourierCoeff_odd_even _ (majority_isOddFunc m) S hS

/-- For an odd set `S`, the Fourier coefficient of majority has the stated binomial formula.
[OD14, Thm. 5.19; Tit62]

**Proof sketch.** Differentiate majority in one coordinate; the derivative is the indicator of the
middle Hamming slice. Evaluate the noise operator on this slice at the all-ones point in two ways:
probabilistically and through its Fourier expansion. Equating polynomial coefficients gives the
formula. -/
theorem majority_fourierCoeff_odd (m : ℕ) (S : Finset (Fin (2 * m + 1)))
    (hS : Odd S.card) :
    fourierCoeff (majority m) S =
      (-1 : ℝ) ^ ((S.card - 1) / 2) *
        (Nat.choose m ((S.card - 1) / 2) / Nat.choose (2 * m) (S.card - 1) : ℝ) *
          (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ) := sorry

/-- Fourier coefficients on complementary odd levels of majority agree up to the sign
`(-1)^m`. [OD14, Cor. 5.20]

**Proof sketch.** Substitute the exact formula from `majority_fourierCoeff_odd` for both sets and
use binomial symmetry after the cardinalities are seen to add to `2m+2`. -/
theorem majority_fourierCoeff_duality (m : ℕ)
    (S T : Finset (Fin (2 * m + 1))) (hcard : S.card + T.card = 2 * m + 2) :
    fourierCoeff (majority m) S = (-1 : ℝ) ^ m * fourierCoeff (majority m) T := by
  have hSle : S.card ≤ 2 * m + 1 := by simpa using Finset.card_le_univ S
  have hTle : T.card ≤ 2 * m + 1 := by simpa using Finset.card_le_univ T
  rcases Nat.even_or_odd S.card with hS | hS
  · have hT : Even T.card := by
      obtain ⟨r, hr⟩ := hS
      exact ⟨m + 1 - r, by omega⟩
    rw [majority_fourierCoeff_even m S hS, majority_fourierCoeff_even m T hT, mul_zero]
  · obtain ⟨p, hp⟩ := hS
    have hq : T.card = 2 * (m - p) + 1 := by omega
    set q : ℕ := m - p with hqdef
    have hpq : p + q = m := by omega
    rw [majority_fourierCoeff_odd m S ⟨p, hp⟩, majority_fourierCoeff_odd m T ⟨q, hq⟩]
    have hp1 : (S.card - 1) / 2 = p := by omega
    have hp2 : S.card - 1 = 2 * p := by omega
    have hq1 : (T.card - 1) / 2 = q := by omega
    have hq2 : T.card - 1 = 2 * q := by omega
    rw [hp1, hp2, hq1, hq2]
    have hcp : Nat.choose m q = Nat.choose m p := by
      have hqm : q = m - p := hqdef
      rw [hqm, Nat.choose_symm (by omega)]
    have hc2 : Nat.choose (2 * m) (2 * q) = Nat.choose (2 * m) (2 * p) := by
      have h2q : 2 * q = 2 * m - 2 * p := by omega
      rw [h2q, Nat.choose_symm (by omega)]
    have hsign : ((-1 : ℝ)) ^ m = (-1 : ℝ) ^ p * (-1 : ℝ) ^ q := by
      rw [← pow_add, hpq]
    have hsq : ((-1 : ℝ)) ^ q * (-1 : ℝ) ^ q = 1 := by
      rw [← pow_add, ← two_mul]
      exact Even.neg_one_pow ⟨q, by ring⟩
    rw [hcp, hc2, hsign]
    have hX : ∀ X : ℝ, (-1 : ℝ) ^ p * X
        = (-1 : ℝ) ^ p * (-1 : ℝ) ^ q * ((-1 : ℝ) ^ q * X) := by
      intro X
      calc (-1 : ℝ) ^ p * X = (-1 : ℝ) ^ p * ((-1 : ℝ) ^ q * (-1 : ℝ) ^ q) * X := by
            rw [hsq, mul_one]
        _ = (-1 : ℝ) ^ p * (-1 : ℝ) ^ q * ((-1 : ℝ) ^ q * X) := by ring
    calc (-1 : ℝ) ^ p * (Nat.choose m p / Nat.choose (2 * m) (2 * p) : ℝ)
            * (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)
        = (-1 : ℝ) ^ p * ((Nat.choose m p / Nat.choose (2 * m) (2 * p) : ℝ)
            * (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)) := by ring
      _ = (-1 : ℝ) ^ p * (-1 : ℝ) ^ q * ((-1 : ℝ) ^ q *
            ((Nat.choose m p / Nat.choose (2 * m) (2 * p) : ℝ)
              * (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ))) := hX _
      _ = (-1 : ℝ) ^ p * (-1 : ℝ) ^ q * ((-1 : ℝ) ^ q
            * (Nat.choose m p / Nat.choose (2 * m) (2 * p) : ℝ)
            * (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)) := by ring

/-- Every even Fourier level of odd-arity majority carries no weight. -/
lemma majority_weightLevel_even (m k : ℕ) (hk : Even k) : weightLevel k (majority m) = 0 := by
  refine Finset.sum_eq_zero fun S _ ↦ ?_
  by_cases hS : S.card = k
  · rw [if_pos hS, majority_fourierCoeff_even m S (hS ▸ hk)]
    norm_num
  · exact if_neg hS

/-- On an odd level all Fourier coefficients of majority share the same absolute value, so the
level weight is the number of sets of that size times the square of the common value. -/
lemma majority_weightLevel_odd (m k : ℕ) (hk : Odd k) :
    weightLevel k (majority m)
      = (Nat.choose (2 * m + 1) k : ℝ) *
        ((Nat.choose m ((k - 1) / 2) / Nat.choose (2 * m) (k - 1) : ℝ) *
          (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)) ^ 2 := by
  classical
  have hfilter : (Finset.univ.filter fun S : Finset (Fin (2 * m + 1)) ↦ S.card = k)
      = Finset.powersetCard k Finset.univ := by
    ext S
    simp
  have hcount : (Finset.univ.filter fun S : Finset (Fin (2 * m + 1)) ↦ S.card = k).card
      = Nat.choose (2 * m + 1) k := by
    rw [hfilter, Finset.card_powersetCard]
    simp
  have hsign : (((-1 : ℝ)) ^ ((k - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨(k - 1) / 2, by ring⟩
  have hterm : ∀ S : Finset (Fin (2 * m + 1)), S.card = k →
      fourierCoeff (majority m) S ^ 2
        = ((Nat.choose m ((k - 1) / 2) / Nat.choose (2 * m) (k - 1) : ℝ) *
            (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)) ^ 2 := by
    intro S hS
    rw [majority_fourierCoeff_odd m S (hS ▸ hk), hS]
    calc ((-1 : ℝ) ^ ((k - 1) / 2)
            * (Nat.choose m ((k - 1) / 2) / Nat.choose (2 * m) (k - 1) : ℝ)
            * (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)) ^ 2
        = (((-1 : ℝ)) ^ ((k - 1) / 2)) ^ 2 *
            ((Nat.choose m ((k - 1) / 2) / Nat.choose (2 * m) (k - 1) : ℝ)
              * (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)) ^ 2 := by ring
      _ = _ := by rw [hsign, one_mul]
  rw [weightLevel, ← Finset.sum_filter,
    Finset.sum_congr rfl fun S hS ↦ hterm S (Finset.mem_filter.mp hS).2,
    Finset.sum_const, hcount, nsmul_eq_mul]

/-- Complementary Fourier levels of majority are related by the corresponding binomial ratio.
[OD14, Cor. 5.20]

**Proof.** All coefficients on a given odd level have the same absolute value, so each level weight
is a binomial count times that common square; the two counts differ exactly by the factor
`k / (2m + 2 - k)`. -/
theorem majority_weight_duality (m k : ℕ) (hk : k ≤ 2 * m + 1) :
    weightLevel (2 * m + 2 - k) (majority m) =
      (k : ℝ) / (2 * m + 2 - k) * weightLevel k (majority m) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    rw [weightLevel_eq_zero_of_lt (by omega) (majority m)]
    simp
  rcases Nat.even_or_odd k with hke | hko
  · have h1 : Even (2 * m + 2 - k) := by
      obtain ⟨r, hr⟩ := hke
      exact ⟨m + 1 - r, by omega⟩
    rw [majority_weightLevel_even m _ h1, majority_weightLevel_even m k hke]
    ring
  · obtain ⟨p, hp⟩ := hko
    have hpm : p ≤ m := by omega
    have hk' : 2 * m + 2 - k = 2 * (m - p) + 1 := by omega
    set q : ℕ := m - p with hqdef
    have hpq : p + q = m := by omega
    have hkodd : Odd k := ⟨p, hp⟩
    have hk'odd : Odd (2 * m + 2 - k) := ⟨q, hk'⟩
    -- the two common coefficient values agree
    have hidx1 : (k - 1) / 2 = p := by omega
    have hidx2 : k - 1 = 2 * p := by omega
    have hidx3 : (2 * m + 2 - k - 1) / 2 = q := by omega
    have hidx4 : 2 * m + 2 - k - 1 = 2 * q := by omega
    have hcp : Nat.choose m q = Nat.choose m p := by
      have hqm : q = m - p := hqdef
      rw [hqm, Nat.choose_symm hpm]
    have hc2 : Nat.choose (2 * m) (2 * q) = Nat.choose (2 * m) (2 * p) := by
      have h2q : 2 * q = 2 * m - 2 * p := by omega
      rw [h2q, Nat.choose_symm (by omega)]
    -- the binomial count on the two levels
    have hsymm : Nat.choose (2 * m + 1) (2 * m + 2 - k) = Nat.choose (2 * m + 1) (k - 1) := by
      have h : k - 1 = 2 * m + 1 - (2 * m + 2 - k) := by omega
      rw [h, Nat.choose_symm (by omega)]
    have hratio : ((2 * m + 2 - k : ℕ) : ℝ) * (Nat.choose (2 * m + 1) (k - 1) : ℝ)
        = (k : ℝ) * (Nat.choose (2 * m + 1) k : ℝ) := by
      have hnat : Nat.choose (2 * m + 1) k * k
          = Nat.choose (2 * m + 1) (k - 1) * (2 * m + 2 - k) := by
        have h := Nat.choose_succ_right_eq (2 * m + 1) (k - 1)
        have h1 : k - 1 + 1 = k := by omega
        have h2 : 2 * m + 1 - (k - 1) = 2 * m + 2 - k := by omega
        rw [h1, h2] at h
        exact h
      have hcastnat := congrArg (fun t : ℕ ↦ (t : ℝ)) hnat
      simp only [Nat.cast_mul] at hcastnat
      linear_combination -hcastnat
    have hden : ((2 : ℝ) * m + 2 - k) ≠ 0 := by
      have hkR : (k : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hk
      intro hcon
      linarith
    have hcast : ((2 * m + 2 - k : ℕ) : ℝ) = 2 * (m : ℝ) + 2 - (k : ℝ) := by
      rw [Nat.cast_sub (by omega : k ≤ 2 * m + 2)]
      push_cast
      ring
    have hratio' : (2 * (m : ℝ) + 2 - (k : ℝ)) * (Nat.choose (2 * m + 1) (k - 1) : ℝ)
        = (k : ℝ) * (Nat.choose (2 * m + 1) k : ℝ) := by
      rw [← hcast]
      exact hratio
    rw [majority_weightLevel_odd m _ hk'odd, majority_weightLevel_odd m k hkodd,
      hidx1, hidx2, hidx3, hidx4, hcp, hc2, hsymm]
    conv_rhs => rw [div_mul_eq_mul_div]
    rw [eq_div_iff hden]
    linear_combination (((Nat.choose m p / Nat.choose (2 * m) (2 * p) : ℝ)
      * (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)) ^ 2) * hratio'

/-! ## Monotonicity and asymptotics -/

/-- For every fixed odd level present in the smaller cube, majority's level weight strictly
decreases when two variables are added. [OD14, Cor. 5.21]

**Proof sketch.** Insert the exact binomial expression for the level weight and simplify the ratio
between consecutive odd dimensions. Every remaining factor is strictly less than one. -/
theorem majority_weight_strictAnti (m k : ℕ) (hkodd : Odd k) (hk : k ≤ 2 * m + 1) :
    weightLevel k (majority (m + 1)) < weightLevel k (majority m) := by
  obtain ⟨p, hp⟩ := hkodd
  have hpm : p ≤ m := by omega
  set u : ℕ := m + 1 - p with hudef
  set v : ℕ := 2 * u - 1 with hvdef
  have hu1 : 1 ≤ u := by omega
  have hum : u ≤ m + 1 := by omega
  have hv1 : 1 ≤ v := by omega
  -- the four binomial recurrences
  have nat1 : Nat.choose (2 * m + 3) k * (2 * u) * v
      = Nat.choose (2 * m + 1) k * (2 * m + 3) * (2 * m + 2) := by
    have e1 : Nat.choose (2 * m + 1) k * (2 * m + 1 + 1)
        = Nat.choose (2 * m + 1 + 1) k * (2 * m + 1 + 1 - k) :=
      Nat.choose_mul_succ_eq (2 * m + 1) k
    have e2 : Nat.choose (2 * m + 2) k * (2 * m + 2 + 1)
        = Nat.choose (2 * m + 2 + 1) k * (2 * m + 2 + 1 - k) :=
      Nat.choose_mul_succ_eq (2 * m + 2) k
    have h1 : 2 * m + 1 + 1 - k = v := by omega
    have h2 : 2 * m + 2 + 1 - k = 2 * u := by omega
    have h3 : 2 * m + 1 + 1 = 2 * m + 2 := by ring
    have h4 : 2 * m + 2 + 1 = 2 * m + 3 := by ring
    rw [h1, h3] at e1
    rw [h2, h4] at e2
    calc Nat.choose (2 * m + 3) k * (2 * u) * v
        = Nat.choose (2 * m + 3) k * (2 * u) * v := rfl
      _ = (Nat.choose (2 * m + 2) k * (2 * m + 3)) * v := by rw [e2]
      _ = (Nat.choose (2 * m + 2) k * v) * (2 * m + 3) := by ring
      _ = (Nat.choose (2 * m + 1) k * (2 * m + 2)) * (2 * m + 3) := by rw [e1]
      _ = Nat.choose (2 * m + 1) k * (2 * m + 3) * (2 * m + 2) := by ring
  have nat2 : Nat.choose m p * (m + 1) = Nat.choose (m + 1) p * u := by
    have e := Nat.choose_mul_succ_eq m p
    have h1 : m + 1 - p = u := by omega
    rw [h1] at e
    exact e
  have nat3 : Nat.choose (2 * m) (2 * p) * (2 * m + 1) * (2 * m + 2)
      = Nat.choose (2 * m + 2) (2 * p) * (2 * u) * v := by
    have e1 : Nat.choose (2 * m) (2 * p) * (2 * m + 1)
        = Nat.choose (2 * m + 1) (2 * p) * (2 * m + 1 - 2 * p) :=
      Nat.choose_mul_succ_eq (2 * m) (2 * p)
    have e2 : Nat.choose (2 * m + 1) (2 * p) * (2 * m + 1 + 1)
        = Nat.choose (2 * m + 1 + 1) (2 * p) * (2 * m + 1 + 1 - 2 * p) :=
      Nat.choose_mul_succ_eq (2 * m + 1) (2 * p)
    have h1 : 2 * m + 1 - 2 * p = v := by omega
    have h2 : 2 * m + 1 + 1 - 2 * p = 2 * u := by omega
    have h3 : 2 * m + 1 + 1 = 2 * m + 2 := by ring
    rw [h1] at e1
    rw [h2, h3] at e2
    calc Nat.choose (2 * m) (2 * p) * (2 * m + 1) * (2 * m + 2)
        = (Nat.choose (2 * m + 1) (2 * p) * v) * (2 * m + 2) := by rw [e1]
      _ = (Nat.choose (2 * m + 1) (2 * p) * (2 * m + 2)) * v := by ring
      _ = Nat.choose (2 * m + 2) (2 * p) * (2 * u) * v := by rw [e2]
  have nat4 : Nat.choose (2 * m + 2) (m + 1) * (m + 1)
      = 2 * Nat.choose (2 * m) m * (2 * m + 1) := by
    have hpascal : Nat.choose (2 * m + 2) (m + 1)
        = Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) :=
      Nat.choose_succ_succ (2 * m + 1) m
    have hsymm : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
      have h := Nat.choose_symm (show m + 1 ≤ 2 * m + 1 by omega)
      have h2 : 2 * m + 1 - (m + 1) = m := by omega
      rw [h2] at h
      exact h.symm
    have e : Nat.choose (2 * m) m * (2 * m + 1) = Nat.choose (2 * m + 1) m * (2 * m + 1 - m) :=
      Nat.choose_mul_succ_eq (2 * m) m
    have h1 : 2 * m + 1 - m = m + 1 := by omega
    rw [h1] at e
    rw [hpascal, hsymm]
    calc (Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) m) * (m + 1)
        = 2 * (Nat.choose (2 * m + 1) m * (m + 1)) := by ring
      _ = 2 * (Nat.choose (2 * m) m * (2 * m + 1)) := by rw [e]
      _ = 2 * Nat.choose (2 * m) m * (2 * m + 1) := by ring
  -- positivity of the binomial coefficients involved
  have hA0 : 0 < Nat.choose (2 * m + 1) k := Nat.choose_pos hk
  have hB0 : 0 < Nat.choose m p := Nat.choose_pos hpm
  have hC0 : 0 < Nat.choose (2 * m) (2 * p) := Nat.choose_pos (by omega)
  have hD0 : 0 < Nat.choose (2 * m) m := Nat.choose_pos (by omega)
  have hC1 : 0 < Nat.choose (2 * m + 2) (2 * p) := Nat.choose_pos (by omega)
  -- move to the reals
  set A0 : ℝ := (Nat.choose (2 * m + 1) k : ℝ) with hA0def
  set A1 : ℝ := (Nat.choose (2 * m + 3) k : ℝ) with hA1def
  set B0 : ℝ := (Nat.choose m p : ℝ) with hB0def
  set B1 : ℝ := (Nat.choose (m + 1) p : ℝ) with hB1def
  set C0 : ℝ := (Nat.choose (2 * m) (2 * p) : ℝ) with hC0def
  set C1 : ℝ := (Nat.choose (2 * m + 2) (2 * p) : ℝ) with hC1def
  set D0 : ℝ := (Nat.choose (2 * m) m : ℝ) with hD0def
  set D1 : ℝ := (Nat.choose (2 * m + 2) (m + 1) : ℝ) with hD1def
  have hUR : (u : ℝ) = (m : ℝ) + 1 - (p : ℝ) := by
    rw [hudef, Nat.cast_sub (by omega : p ≤ m + 1)]
    push_cast
    ring
  have hVR : (v : ℝ) = 2 * (u : ℝ) - 1 := by
    rw [hvdef, Nat.cast_sub (by omega : 1 ≤ 2 * u)]
    push_cast
    ring
  have hUpos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu1
  have hVpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
  have hA0pos : (0 : ℝ) < A0 := by rw [hA0def]; exact_mod_cast hA0
  have hB0pos : (0 : ℝ) < B0 := by rw [hB0def]; exact_mod_cast hB0
  have hC0pos : (0 : ℝ) < C0 := by rw [hC0def]; exact_mod_cast hC0
  have hD0pos : (0 : ℝ) < D0 := by rw [hD0def]; exact_mod_cast hD0
  have hC1pos : (0 : ℝ) < C1 := by rw [hC1def]; exact_mod_cast hC1
  have I1 : A1 * (2 * (u : ℝ)) * (v : ℝ) = A0 * (2 * (m : ℝ) + 3) * (2 * (m : ℝ) + 2) := by
    have := congrArg (fun t : ℕ ↦ (t : ℝ)) nat1
    push_cast at this
    rw [hA0def, hA1def]
    linear_combination this
  have I2 : B0 * ((m : ℝ) + 1) = B1 * (u : ℝ) := by
    have := congrArg (fun t : ℕ ↦ (t : ℝ)) nat2
    push_cast at this
    rw [hB0def, hB1def]
    linear_combination this
  have I3 : C0 * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2) = C1 * (2 * (u : ℝ)) * (v : ℝ) := by
    have := congrArg (fun t : ℕ ↦ (t : ℝ)) nat3
    push_cast at this
    rw [hC0def, hC1def]
    linear_combination this
  have I4 : D1 * ((m : ℝ) + 1) = 2 * D0 * (2 * (m : ℝ) + 1) := by
    have := congrArg (fun t : ℕ ↦ (t : ℝ)) nat4
    push_cast at this
    rw [hD0def, hD1def]
    linear_combination this
  -- solve the recurrences for the larger-dimension quantities
  have hA1eq : A1 = A0 * (2 * (m : ℝ) + 3) * (2 * (m : ℝ) + 2) / ((2 * (u : ℝ)) * (v : ℝ)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination I1
  have hB1eq : B1 = B0 * ((m : ℝ) + 1) / (u : ℝ) := by
    rw [eq_div_iff (ne_of_gt hUpos)]
    linear_combination -I2
  have hC1eq : C1 = C0 * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2) / ((2 * (u : ℝ)) * (v : ℝ)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination -I3
  have hD1eq : D1 = 2 * D0 * (2 * (m : ℝ) + 1) / ((m : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    linear_combination I4
  -- the level weights, and the exact ratio between them
  have hidx1 : (k - 1) / 2 = p := by omega
  have hidx2 : k - 1 = 2 * p := by omega
  have harity : 2 * (m + 1) = 2 * m + 2 := by ring
  have harity' : 2 * m + 2 + 1 = 2 * m + 3 := by ring
  rw [majority_weightLevel_odd (m + 1) k ⟨p, hp⟩, majority_weightLevel_odd m k ⟨p, hp⟩,
    hidx1, hidx2, harity, harity']
  rw [← hA0def, ← hA1def, ← hB0def, ← hB1def, ← hC0def, ← hC1def, ← hD0def, ← hD1def]
  have hpow : (2 : ℝ) ^ (2 * m + 2) = 2 ^ (2 * m) * 4 := by
    rw [pow_add]
    norm_num
  have hpowpos : (0 : ℝ) < 2 ^ (2 * m) := by positivity
  have hMpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hratio : A1 * (B1 / C1 * (D1 / 2 ^ (2 * m + 2))) ^ 2 * (4 * (u : ℝ) * ((m : ℝ) + 1))
      = A0 * (B0 / C0 * (D0 / 2 ^ (2 * m))) ^ 2 * ((2 * (m : ℝ) + 3) * (v : ℝ)) := by
    rw [hA1eq, hB1eq, hC1eq, hD1eq, hpow]
    field_simp
    ring
  have hRHSpos : (0 : ℝ) < A0 * (B0 / C0 * (D0 / 2 ^ (2 * m))) ^ 2 := by positivity
  have hstrict : (2 * (m : ℝ) + 3) * (v : ℝ) < 4 * (u : ℝ) * ((m : ℝ) + 1) := by
    have humR : (u : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hum
    rw [hVR]
    nlinarith [hUpos, humR]
  have hposfac : (0 : ℝ) < 4 * (u : ℝ) * ((m : ℝ) + 1) := by positivity
  have hlt : A1 * (B1 / C1 * (D1 / 2 ^ (2 * m + 2))) ^ 2 * (4 * (u : ℝ) * ((m : ℝ) + 1))
      < A0 * (B0 / C0 * (D0 / 2 ^ (2 * m))) ^ 2 * (4 * (u : ℝ) * ((m : ℝ) + 1)) := by
    rw [hratio]
    exact mul_lt_mul_of_pos_left hstrict hRHSpos
  exact lt_of_mul_lt_mul_right (by linarith [hlt]) (le_of_lt hposfac)

/-- Each fixed odd Fourier level of majority converges to the matching coefficient in
`(2/π) * arcsin ρ`, with the chapter's finite-dimensional error bound.
[OD14, Thm. 5.22]

**Proof sketch.** Divide the exact level-weight formula by `majorityLimitWeight k`. The quotient is
a ratio of normalized central binomial coefficients, which increases to one by Stirling's formula.
Elementary estimates on the quotient yield the explicit factor `1 + 2k/n`. -/
theorem majority_weight_tendsto (k : ℕ) (hkodd : Odd k) :
    Filter.Tendsto (fun m : ℕ ↦ weightLevel k (majority m)) Filter.atTop
      (nhds (majorityLimitWeight k)) ∧
    ∀ m : ℕ, k ≤ (2 * m + 1) / 2 →
      majorityLimitWeight k ≤ weightLevel k (majority m) ∧
        weightLevel k (majority m) ≤
          (1 + 2 * (k : ℝ) / (2 * m + 1)) * majorityLimitWeight k := sorry

/-- The total Fourier weight of majority on the levels below `j` decreases when two variables are
added. -/
lemma majority_prefix_weight_le (m : ℕ) :
    ∀ j, j ≤ 2 * (m + 1) + 2 →
      ∑ k ∈ Finset.range j, weightLevel k (majority (m + 1))
        ≤ ∑ k ∈ Finset.range j, weightLevel k (majority m) := by
  intro j hj
  have hterm : ∀ k, k ≤ 2 * m + 1 →
      weightLevel k (majority (m + 1)) ≤ weightLevel k (majority m) := by
    intro k hk
    rcases Nat.even_or_odd k with hkev | hkodd
    · rw [majority_weightLevel_even _ _ hkev, majority_weightLevel_even _ _ hkev]
    · exact le_of_lt (majority_weight_strictAnti m k hkodd hk)
  rcases le_or_gt j (2 * m + 2) with hjle | hjgt
  · refine Finset.sum_le_sum fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    exact hterm k (by omega)
  · -- beyond level `2m+1` the smaller majority has no weight left, so its prefix is already `1`
    have ha : ∑ k ∈ Finset.range j, weightLevel k (majority m) = 1 := by
      have hsub : Finset.range (2 * m + 1 + 1) ⊆ Finset.range j :=
        GCongr.finset_range_subset_of_le (show 2 * m + 1 + 1 ≤ j by omega)
      have hzero : ∀ k ∈ Finset.range j, k ∉ Finset.range (2 * m + 1 + 1) →
          weightLevel k (majority m) = 0 := by
        intro k _ hk
        rw [Finset.mem_range] at hk
        exact weightLevel_eq_zero_of_lt (by omega) _
      rw [← Finset.sum_subset hsub hzero]
      exact sum_weightLevel_eq_one (majority_isPmOne m)
    have hb : ∑ k ∈ Finset.range j, weightLevel k (majority (m + 1)) ≤ 1 := by
      have hsub : Finset.range j ⊆ Finset.range (2 * (m + 1) + 1 + 1) :=
        GCongr.finset_range_subset_of_le (show j ≤ 2 * (m + 1) + 1 + 1 by omega)
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ ↦ weightLevel_nonneg k (majority (m + 1)))
      rwa [sum_weightLevel_eq_one (majority_isPmOne (m + 1))] at hle
    rw [ha]
    exact hb

/-- At nonnegative correlation the noise stability of majority decreases as two variables are
added. [OD14, Cor. 5.21] -/
theorem majority_noiseStability_antitone {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (m : ℕ) :
    noiseStability ρ (majority (m + 1)) ≤ noiseStability ρ (majority m) := by
  have hNa : ∀ g : ℕ → ℝ, ∑ k ∈ Finset.range (2 * m + 1 + 1), g k * weightLevel k (majority m)
      = ∑ k ∈ Finset.range (2 * (m + 1) + 2), g k * weightLevel k (majority m) := by
    intro g
    refine Finset.sum_subset
      (GCongr.finset_range_subset_of_le (show 2 * m + 1 + 1 ≤ 2 * (m + 1) + 2 by omega)) fun k _ hk ↦ ?_
    rw [Finset.mem_range] at hk
    rw [weightLevel_eq_zero_of_lt (by omega) (majority m), mul_zero]
  have hstaba : noiseStability ρ (majority m)
      = ∑ k ∈ Finset.range (2 * (m + 1) + 2), ρ ^ k * weightLevel k (majority m) := by
    rw [noiseStability_eq_sum_weightLevel]
    exact hNa (fun k ↦ ρ ^ k)
  have hstabb : noiseStability ρ (majority (m + 1))
      = ∑ k ∈ Finset.range (2 * (m + 1) + 2), ρ ^ k * weightLevel k (majority (m + 1)) := by
    rw [noiseStability_eq_sum_weightLevel]
  have htot : ∑ k ∈ Finset.range (2 * (m + 1) + 2), weightLevel k (majority (m + 1))
      = ∑ k ∈ Finset.range (2 * (m + 1) + 2), weightLevel k (majority m) := by
    rw [sum_weightLevel_eq_one (majority_isPmOne (m + 1))]
    have h := hNa (fun _ ↦ (1 : ℝ))
    simp only [one_mul] at h
    rw [← h, sum_weightLevel_eq_one (majority_isPmOne m)]
  rw [hstaba, hstabb]
  exact sum_pow_mul_le_of_prefix_le hρ0 hρ1 _ _ (majority_prefix_weight_le m) htot

/-- Uniformly when odd `k` grows and the odd majority arity `n = 2m+1` is at least `2k²`, the
level-`k` weight and the tail above `k` have the Chapter 5 asymptotics. The existential constant is
an explicit rendering of the two `O(1/k)` terms. [OD14, Cor. 5.23]

**Proof sketch.** Apply `majority_weight_tendsto` uniformly under the dimension hypothesis, estimate
the limiting binomial coefficient by Stirling's formula, and compare the sum of odd-level tails with
the integral of `x⁻³ᐟ²`. -/
theorem majority_weight_asymptotics :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m k : ℕ, Odd k → 0 < k → 2 * k ^ 2 ≤ 2 * m + 1 →
      |weightLevel k (majority m) /
            ((2 / Real.pi) ^ (3 / 2 : ℝ) * Real.rpow k (-3 / 2 : ℝ)) - 1| ≤ C / k ∧
        |fourierWeightAbove k (majority m) /
            ((2 / Real.pi) ^ (3 / 2 : ℝ) * Real.rpow k (-1 / 2 : ℝ)) - 1| ≤ C / k := sorry

end ThresholdFunctions
end BooleanAnalysis
