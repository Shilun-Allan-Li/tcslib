import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Central
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
  have hD (j : ℕ) (hj : j ≤ N) : 0 ≤ ∑ k ∈ Finset.range j, d k := by
    simp only [hd, Finset.sum_sub_distrib]
    linarith [hpre j hj]
  have hDN : ∑ k ∈ Finset.range N, d k = 0 := by
    simp only [hd, Finset.sum_sub_distrib, htot, sub_self]
  -- Abel summation against the nonincreasing weights `ρ ^ k`.
  have key : ∑ k ∈ Finset.range N, ρ ^ k * d k
      = ∑ i ∈ Finset.range (N - 1), (ρ ^ i - ρ ^ (i + 1)) * ∑ k ∈ Finset.range (i + 1), d k := by
    have h := Finset.sum_range_by_parts (fun k : ℕ ↦ ρ ^ k) d N
    simp only [smul_eq_mul] at h
    rw [h, hDN, mul_zero, zero_sub, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range N, ρ ^ k * d k := by
    rw [key]
    refine Finset.sum_nonneg fun i hi ↦ mul_nonneg ?_ (hD (i + 1) ?_)
    · rw [sub_nonneg, pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hρ0 i) hρ1
    · rw [Finset.mem_range] at hi
      omega
  simp only [hd, mul_sub, Finset.sum_sub_distrib] at hnonneg
  linarith

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

/-- The common magnitude `C(m, p) / C(2m, 2p)` of the level-`(2p+1)` majority coefficients is
invariant under `p ↦ m - p`. -/
private lemma choose_div_choose_symm {m p q : ℕ} (hpq : p + q = m) :
    (Nat.choose m q / Nat.choose (2 * m) (2 * q) : ℝ) =
      Nat.choose m p / Nat.choose (2 * m) (2 * p) := by
  obtain rfl : q = m - p := by omega
  rw [Nat.choose_symm (by omega), show 2 * (m - p) = 2 * m - 2 * p by omega,
    Nat.choose_symm (by omega)]

/-- Fourier coefficients on complementary odd levels of majority agree up to the sign
`(-1)^m`. [OD14, Cor. 5.20]

**Proof sketch.** Substitute the exact formula from `majority_fourierCoeff_odd` for both sets and
use binomial symmetry after the cardinalities are seen to add to `2m+2`. -/
theorem majority_fourierCoeff_duality (m : ℕ)
    (S T : Finset (Fin (2 * m + 1))) (hcard : S.card + T.card = 2 * m + 2) :
    fourierCoeff (majority m) S = (-1 : ℝ) ^ m * fourierCoeff (majority m) T := by
  have hSle : S.card ≤ 2 * m + 1 := by simpa using Finset.card_le_univ S
  rcases Nat.even_or_odd S.card with hS | ⟨p, hp⟩
  · have hT : Even T.card := by
      obtain ⟨r, hr⟩ := hS
      exact ⟨m + 1 - r, by omega⟩
    rw [majority_fourierCoeff_even m S hS, majority_fourierCoeff_even m T hT, mul_zero]
  · obtain ⟨q, hq, hpq⟩ : ∃ q, T.card = 2 * q + 1 ∧ p + q = m := ⟨m - p, by omega, by omega⟩
    rw [majority_fourierCoeff_odd m S ⟨p, hp⟩, majority_fourierCoeff_odd m T ⟨q, hq⟩, hp, hq,
      show (2 * p + 1 - 1) / 2 = p by omega, show 2 * p + 1 - 1 = 2 * p by omega,
      show (2 * q + 1 - 1) / 2 = q by omega, show 2 * q + 1 - 1 = 2 * q by omega,
      choose_div_choose_symm hpq, ← hpq, pow_add]
    have hsq : (-1 : ℝ) ^ q * (-1) ^ q = 1 := by rw [← pow_add]; exact Even.neg_one_pow ⟨q, rfl⟩
    linear_combination (-((-1 : ℝ) ^ p * (Nat.choose (p + q) p / Nat.choose (2 * (p + q)) (2 * p))
      * (Nat.choose (2 * (p + q)) (p + q) / 2 ^ (2 * (p + q))))) * hsq

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
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [weightLevel_eq_zero_of_lt (by omega) (majority m)]
    simp
  rcases Nat.even_or_odd k with hke | ⟨p, rfl⟩
  · have h1 : Even (2 * m + 2 - k) := by
      obtain ⟨r, hr⟩ := hke
      exact ⟨m + 1 - r, by omega⟩
    rw [majority_weightLevel_even m _ h1, majority_weightLevel_even m k hke]
    ring
  obtain ⟨q, hq, hpq⟩ : ∃ q, 2 * m + 2 - (2 * p + 1) = 2 * q + 1 ∧ p + q = m :=
    ⟨m - p, by omega, by omega⟩
  -- The two levels have binomial counts in the ratio `k : (2m + 2 - k)`.
  have hcount : ((2 * q + 1 : ℕ) : ℝ) * Nat.choose (2 * m + 1) (2 * q + 1)
      = ((2 * p + 1 : ℕ) : ℝ) * Nat.choose (2 * m + 1) (2 * p + 1) := by
    have h := Nat.choose_succ_right_eq (2 * m + 1) (2 * p)
    rw [show 2 * m + 1 - 2 * p = 2 * q + 1 by omega,
      ← Nat.choose_symm (show 2 * p ≤ 2 * m + 1 by omega),
      show 2 * m + 1 - 2 * p = 2 * q + 1 by omega] at h
    rw [mul_comm, mul_comm ((2 * p + 1 : ℕ) : ℝ)]
    exact_mod_cast h.symm
  have hden : (2 : ℝ) * m + 2 - (2 * p + 1 : ℕ) = (2 * q + 1 : ℕ) := by
    push_cast; rw [← hpq]; push_cast; ring
  rw [hq, majority_weightLevel_odd m _ ⟨q, rfl⟩, majority_weightLevel_odd m _ ⟨p, rfl⟩,
    show (2 * p + 1 - 1) / 2 = p by omega, show 2 * p + 1 - 1 = 2 * p by omega,
    show (2 * q + 1 - 1) / 2 = q by omega, show 2 * q + 1 - 1 = 2 * q by omega,
    choose_div_choose_symm hpq, hden]
  conv_rhs => rw [div_mul_eq_mul_div]
  rw [eq_div_iff (by positivity)]
  linear_combination (((Nat.choose m p / Nat.choose (2 * m) (2 * p) : ℝ)
      * (Nat.choose (2 * m) m / 2 ^ (2 * m) : ℝ)) ^ 2) * hcount

/-! ## Monotonicity and asymptotics -/

/-- Two steps of the binomial recurrence `C(n, k) (n + 1) = C(n + 1, k) (n + 1 - k)`, written
without truncated subtraction: if `N = k + a`, then
`C(N + 2, k) (a + 2)(a + 1) = C(N, k) (N + 2)(N + 1)`. -/
private lemma choose_add_two_mul {N k a : ℕ} (h : N = k + a) :
    (N + 2).choose k * ((a + 2) * (a + 1)) = N.choose k * ((N + 2) * (N + 1)) := by
  subst h
  have e1 := Nat.choose_mul_succ_eq (k + a) k
  have e2 := Nat.choose_mul_succ_eq (k + a + 1) k
  rw [show k + a + 1 - k = a + 1 by omega] at e1
  rw [show k + a + 1 + 1 - k = a + 2 by omega] at e2
  calc (k + a + 2).choose k * ((a + 2) * (a + 1))
      = (k + a + 1 + 1).choose k * (a + 2) * (a + 1) := by ring
    _ = (k + a + 1).choose k * (a + 1) * (k + a + 2) := by rw [← e2]; ring
    _ = (k + a).choose k * ((k + a + 2) * (k + a + 1)) := by rw [← e1]; ring

/-- For every fixed odd level present in the smaller cube, majority's level weight strictly
decreases when two variables are added. [OD14, Cor. 5.21]

**Proof sketch.** Insert the exact binomial expression for the level weight and simplify the ratio
between consecutive odd dimensions. Every remaining factor is strictly less than one. -/
theorem majority_weight_strictAnti (m k : ℕ) (hkodd : Odd k) (hk : k ≤ 2 * m + 1) :
    weightLevel k (majority (m + 1)) < weightLevel k (majority m) := by
  obtain ⟨p, rfl⟩ := hkodd
  obtain ⟨w, rfl⟩ : ∃ w, m = p + w := ⟨m - p, by omega⟩
  -- The four binomial recurrences relating the two dimensions, cast to `ℝ`.
  have I1 : ((2 * (p + w) + 3).choose (2 * p + 1) : ℝ) * ((2 * w + 2) * (2 * w + 1)) =
      (2 * (p + w) + 1).choose (2 * p + 1) * ((2 * (p + w) + 3) * (2 * (p + w) + 2)) := by
    exact_mod_cast choose_add_two_mul (N := 2 * (p + w) + 1) (a := 2 * w) (by ring)
  have I2 : ((p + w).choose p : ℝ) * ((p + w) + 1) = (p + w + 1).choose p * (w + 1) := by
    have h := Nat.choose_mul_succ_eq (p + w) p
    rw [show p + w + 1 - p = w + 1 by omega] at h
    exact_mod_cast h
  have I3 : ((2 * (p + w) + 2).choose (2 * p) : ℝ) * ((2 * w + 2) * (2 * w + 1)) =
      (2 * (p + w)).choose (2 * p) * ((2 * (p + w) + 2) * (2 * (p + w) + 1)) := by
    exact_mod_cast choose_add_two_mul (N := 2 * (p + w)) (a := 2 * w) (by ring)
  have I4 : ((2 * (p + w) + 2).choose (p + w + 1) : ℝ) * ((p + w) + 1) =
      2 * (2 * (p + w)).choose (p + w) * (2 * (p + w) + 1) := by
    have h := Nat.succ_mul_centralBinom_succ (p + w)
    rw [Nat.centralBinom, Nat.centralBinom, show 2 * (p + w + 1) = 2 * (p + w) + 2 by ring] at h
    have h' : ((p + w + 1 : ℕ) : ℝ) * (2 * (p + w) + 2).choose (p + w + 1) =
        2 * (2 * (p + w) + 1 : ℕ) * (2 * (p + w)).choose (p + w) := by exact_mod_cast h
    push_cast at h'
    linear_combination h'
  -- Positivity of the binomial coefficients in the smaller dimension.
  have hA : (0 : ℝ) < (2 * (p + w) + 1).choose (2 * p + 1) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hB : (0 : ℝ) < (p + w).choose p := by exact_mod_cast Nat.choose_pos (by omega)
  have hC : (0 : ℝ) < (2 * (p + w)).choose (2 * p) := by exact_mod_cast Nat.choose_pos (by omega)
  have hD : (0 : ℝ) < (2 * (p + w)).choose (p + w) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [majority_weightLevel_odd (p + w + 1) _ ⟨p, rfl⟩, majority_weightLevel_odd (p + w) _ ⟨p, rfl⟩,
    show (2 * p + 1 - 1) / 2 = p by omega, show 2 * p + 1 - 1 = 2 * p by omega,
    show 2 * (p + w + 1) + 1 = 2 * (p + w) + 3 by ring,
    show 2 * (p + w + 1) = 2 * (p + w) + 2 by ring]
  generalize ((2 * (p + w) + 3).choose (2 * p + 1) : ℝ) = A₁ at I1 ⊢
  generalize ((2 * (p + w) + 1).choose (2 * p + 1) : ℝ) = A₀ at I1 hA ⊢
  generalize ((p + w + 1).choose p : ℝ) = B₁ at I2 ⊢
  generalize ((p + w).choose p : ℝ) = B₀ at I2 hB ⊢
  generalize ((2 * (p + w) + 2).choose (2 * p) : ℝ) = C₁ at I3 ⊢
  generalize ((2 * (p + w)).choose (2 * p) : ℝ) = C₀ at I3 hC ⊢
  generalize ((2 * (p + w) + 2).choose (p + w + 1) : ℝ) = D₁ at I4 ⊢
  generalize ((2 * (p + w)).choose (p + w) : ℝ) = D₀ at I4 hD ⊢
  -- Solve the recurrences for the binomial coefficients in the larger dimension.
  have hA₁ : A₁ = A₀ * ((2 * (p + w) + 3) * (2 * (p + w) + 2)) / ((2 * w + 2) * (2 * w + 1)) := by
    rw [eq_div_iff (by positivity)]; exact I1
  have hB₁ : B₁ = B₀ * (p + w + 1) / (w + 1) := by
    rw [eq_div_iff (by positivity)]; exact I2.symm
  have hC₁ : C₁ = C₀ * ((2 * (p + w) + 2) * (2 * (p + w) + 1)) / ((2 * w + 2) * (2 * w + 1)) := by
    rw [eq_div_iff (by positivity)]; exact I3
  have hD₁ : D₁ = 2 * D₀ * (2 * (p + w) + 1) / (p + w + 1) := by
    rw [eq_div_iff (by positivity)]; exact I4
  subst hA₁ hB₁ hC₁ hD₁
  -- The ratio of the two level weights is `(2m + 3)(2w + 1) / ((2w + 2)(2m + 2)) < 1`.
  set W₀ := A₀ * (B₀ / C₀ * (D₀ / 2 ^ (2 * (p + w)))) ^ 2 with hW₀def
  have hW₀ : 0 < W₀ := mul_pos hA (pow_pos (mul_pos (div_pos hB hC) (div_pos hD (by positivity))) 2)
  calc _ = W₀ * ((2 * (p + w) + 3) * (2 * w + 1) / ((2 * w + 2) * (2 * (p + w) + 2))) := by
        rw [pow_add, hW₀def]
        field_simp
    _ < W₀ := by
        refine mul_lt_of_lt_one_right hW₀ ((div_lt_one (by positivity)).mpr ?_)
        nlinarith

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
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun k _ hk ↦ ?_
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
