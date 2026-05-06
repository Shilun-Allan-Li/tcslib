import Mathlib
import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.LMN

/-!
# Helper lemmas for the LMN bound

Auxiliary results needed for the main LMN bound proof.
These supplement the helper lemmas already in `LMN.lean`.
-/

open BooleanAnalysis SwitchingLemma2
open scoped BigOperators
open Classical in
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 400000

noncomputable section

namespace LMN

variable {n : ℕ}

/-! ## Binomial distribution helpers -/

/-- The binomial probability mass function: `C(m, k) * p^k * (1-p)^(m-k)`. -/
def binomialPMF (m : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k)

/-
The binomial weights sum to 1.
-/
lemma binomial_sum_eq_one (m : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (m + 1), binomialPMF m p k = 1 := by
  unfold binomialPMF;
  have := add_pow p ( 1 - p ) m;
  simpa [ mul_assoc, mul_comm, mul_left_comm ] using this.symm

/-
The expected value of a Binomial(m, p) random variable is `m * p`.
-/
lemma binomial_expectation (m : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (m + 1), binomialPMF m p k * (k : ℝ) = (m : ℝ) * p := by
  have h_exp : ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) * k = m * p * ∑ k ∈ Finset.range m, (Nat.choose (m - 1) k : ℝ) * p ^ k * (1 - p) ^ (m - 1 - k) := by
    rw [ Finset.sum_range_succ' ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    refine Finset.sum_congr rfl fun x hx => ?_;
    rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Finset.mem_range.mp hx ];
    · rcases m with ( _ | m ) <;> simp_all +decide [ Nat.factorial, mul_assoc, mul_comm, mul_left_comm, tsub_tsub ];
      -- Combine and simplify the fractions
      field_simp
      ring;
    · exact Nat.le_pred_of_lt ( Finset.mem_range.mp hx );
  have := binomial_sum_eq_one ( m - 1 ) p;
  cases m <;> simp_all +decide [ binomialPMF ]

/-
The variance of a Binomial(m, p) random variable is `m * p * (1 - p)`.
-/
lemma binomial_variance (m : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (m + 1), binomialPMF m p k * ((k : ℝ) - (m : ℝ) * p) ^ 2 =
    (m : ℝ) * p * (1 - p) := by
  -- We'll use the fact that $\sum_{k=0}^{m} \binom{m}{k} p^k (1-p)^{m-k} k^2 = m p (m p + 1 - p)$.
  have sum_k2 : ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (k : ℝ) ^ 2 = m * p * (m * p + 1 - p) := by
    have sum_k2 : ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (k : ℝ) ^ 2 = m * p * (∑ k ∈ Finset.range (m), (Nat.choose (m - 1) k : ℝ) * p ^ k * (1 - p) ^ (m - 1 - k) * (k + 1)) := by
      rw [ Finset.sum_range_succ' ];
      rcases m <;> simp_all +decide [ Nat.add_one_mul_choose_eq, pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun x hx => _;
      rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Finset.mem_range.mp hx ];
      field_simp;
      rw [ Nat.succ_sub_succ ] ; push_cast [ Nat.factorial_succ ] ; ring;
    rcases m with ( _ | m ) <;> simp_all +decide [ Finset.sum_add_distrib, mul_add ];
    -- We'll use the fact that $\sum_{k=0}^{m} \binom{m}{k} p^k (1-p)^{m-k} k = m p$.
    have sum_k : ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (k : ℝ) = m * p := by
      convert binomial_expectation m p using 1;
    have sum_const : ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) = (p + (1 - p)) ^ m := by
      rw [ add_pow ] ; congr ; ext ; ring;
    rw [ sum_k, sum_const ] ; ring;
  convert congr_arg ( fun x : ℝ => x - 2 * ( m * p ) * ( ∑ k ∈ Finset.range ( m + 1 ), ( Nat.choose m k : ℝ ) * p ^ k * ( 1 - p ) ^ ( m - k ) * ( k : ℝ ) ) + ( m * p ) ^ 2 * ( ∑ k ∈ Finset.range ( m + 1 ), ( Nat.choose m k : ℝ ) * p ^ k * ( 1 - p ) ^ ( m - k ) ) ) sum_k2 using 1;
  · norm_num [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, sub_sq, binomialPMF ];
    simpa only [ ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun _ _ => by ring;
  · have sum_k : ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * p ^ k * (1 - p) ^ (m - k) * (k : ℝ) = m * p := by
      convert binomial_expectation m p using 1;
    rw [ sum_k, show ( ∑ k ∈ Finset.range ( m + 1 ), ( m.choose k : ℝ ) * p ^ k * ( 1 - p ) ^ ( m - k ) ) = 1 from ?_ ] ; ring;
    convert binomial_sum_eq_one m p using 1

/-
Discrete Chebyshev bound: for Binomial(m, p) with `m * p ≥ 8`,
    the probability that X ≤ `m * p / 2` is at most 1/2.
    Proof: By Chebyshev's inequality, Pr[X ≤ mp/2] ≤ Var(X)/((mp - mp/2)²)
    = mp(1-p)/((mp/2)²) = 4(1-p)/(mp) ≤ 4/8 = 1/2.
-/
lemma binomial_chebyshev_lower_tail (m : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hmp : 8 ≤ (m : ℝ) * p) :
    ∑ k ∈ Finset.range (m + 1),
      binomialPMF m p k * (if (k : ℝ) ≤ (m : ℝ) * p / 2 then (1 : ℝ) else (0 : ℝ)) ≤ 1 / 2 := by
  -- By Chebyshev's inequality, we have $P(X \leq mp/2) \leq \frac{\text{Var}(X)}{(mp/2)^2}$.
  have h_chebyshev : (∑ k ∈ Finset.range (m + 1), binomialPMF m p k * if (k : ℝ) ≤ m * p / 2 then 1 else 0) ≤ (∑ k ∈ Finset.range (m + 1), binomialPMF m p k * ((k : ℝ) - m * p) ^ 2) / (m * p / 2) ^ 2 := by
    rw [ Finset.sum_div _ _ _ ];
    refine Finset.sum_le_sum fun i hi => ?_;
    split_ifs <;> norm_num;
    · rw [ le_div_iff₀ ( by positivity ) ];
      exact mul_le_mul_of_nonneg_left ( by nlinarith ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp.le _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1.le ) _ ) );
    · exact div_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp.le _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1.le ) _ ) ) ( sq_nonneg _ ) ) ( sq_nonneg _ );
  refine le_trans h_chebyshev ?_;
  rw [ div_le_iff₀ ] <;> nlinarith [ binomial_variance m p, mul_pos hp ( show 0 < ( m : ℝ ) by norm_cast; contrapose! hmp; aesop ) ]

end LMN

end
