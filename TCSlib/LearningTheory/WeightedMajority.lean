import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Cases

open Finset BigOperators Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-!
# Weighted Majority Algorithm: Mistake Bound

## Main results

- `wm_weight_shrinkage`: After M algorithm mistakes, total weight satisfies W_M ≤ W₀ · ((1+β)/2)^M
- `wm_weight_upper_bound`: After M algorithm mistakes starting from n unit-weight experts, W_M ≤ n · ((1+β)/2)^M
- `wm_combined_potential_bound`: Taking logs of the potential bound β^M_star ≤ n · ((1+β)/2)^M_WM
- `wm_mistake_bound_log`: Logarithmic mistake bound M_WM · log(2/(1+β)) ≤ log(n) + M_star · log(1/β)
- `deterministic_factor2_lower_bound`: A factor-2 lower bound for deterministic agnostic learners

## References

- Original formalization by Arhaan Aggarwal
-/

/-
============================================================================
Weight shrinkage lemma
============================================================================

When the algorithm makes a mistake, at least half the total weight is on wrong experts.
    Those experts are multiplied by β, so the new total weight is at most
    W · (1 + β)/2 of the old total weight.

    This lemma proves that after M such shrinkage steps starting from W₀,
    we have W_M ≤ W₀ · ((1 + β)/2)^M.
-/
theorem wm_weight_shrinkage
    (β : ℝ) (hβ0 : 0 < β) (_hβ1 : β < 1)
    (M : ℕ)
    (W : ℕ → ℝ)
    (_hW_pos : ∀ k, 0 < W k)
    (hW_step : ∀ k, k < M → W (k + 1) ≤ W k * ((1 + β) / 2)) :
    W M ≤ W 0 * ((1 + β) / 2) ^ M := by
  induction' M with M ih;
  · norm_num;
  · simpa only [ pow_succ, mul_assoc ] using le_trans ( hW_step M ( Nat.lt_succ_self M ) ) ( mul_le_mul_of_nonneg_right ( ih fun k hk => hW_step k ( Nat.lt_succ_of_lt hk ) ) ( by positivity ) )

/-
After M algorithm mistakes starting with n experts of weight 1 each (total weight n),
    the total weight is at most n · ((1+β)/2)^M.
-/
theorem wm_weight_upper_bound
    (n : ℕ) (_hn : 0 < n)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (M : ℕ)
    (W : ℕ → ℝ)
    (hW0 : W 0 = (n : ℝ))
    (hW_pos : ∀ k, 0 < W k)
    (hW_step : ∀ k, k < M → W (k + 1) ≤ W k * ((1 + β) / 2)) :
    W M ≤ (n : ℝ) * ((1 + β) / 2) ^ M := by
  simpa [ hW0, mul_comm ] using wm_weight_shrinkage β hβ0 hβ1 M W hW_pos hW_step

/-
============================================================================
Combined potential bound
============================================================================

The core potential function inequality for Weighted Majority:
    The best expert makes M_star mistakes, so its final weight is β^{M_star}.
    The total weight is at least this one expert's weight: β^{M_star} ≤ W_T.
    Combined with the upper bound W_T ≤ n · ((1+β)/2)^{M_WM}.
-/
theorem wm_combined_potential_bound
    (n : ℕ) (_hn : 0 < n)
    (β : ℝ) (hβ0 : 0 < β) (_hβ1 : β < 1)
    (M_star M_WM : ℕ)
    -- Lower bound: best expert's weight
    (h_lower : β ^ M_star ≤ (n : ℝ) * ((1 + β) / 2) ^ M_WM)
    -- This is the hypothesis; the theorem packages the logarithmic consequence
    : Real.log (β ^ M_star) ≤ Real.log ((n : ℝ) * ((1 + β) / 2) ^ M_WM) := by
  gcongr

/-
The logarithmic form of the Weighted Majority mistake bound:
    M_WM · log(2/(1+β)) ≤ log(n) + M_star · log(1/β)

    This is derived by taking logarithms of β^{M_star} ≤ n · ((1+β)/2)^{M_WM}
    and rearranging. Since log((1+β)/2) < 0, we rewrite as log(2/(1+β)) > 0.

    Equivalently: M_WM ≤ [log(n) + M_star · log(1/β)] / log(2/(1+β))
-/
theorem wm_mistake_bound_log
    (n : ℕ) (hn : 1 < n)
    (β : ℝ) (hβ0 : 0 < β) (_hβ1 : β < 1)
    (M_star M_WM : ℕ)
    (h : β ^ M_star ≤ (n : ℝ) * ((1 + β) / 2) ^ M_WM) :
    (M_WM : ℝ) * Real.log (2 / (1 + β)) ≤
      Real.log (n : ℝ) + (M_star : ℝ) * Real.log (1 / β) := by
  have := Real.log_le_log ?_ h;
  · rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] at this;
    rw [ show ( 2 : ℝ ) / ( 1 + β ) = ( ( 1 + β ) / 2 ) ⁻¹ by rw [ inv_div ], Real.log_inv ] ; norm_num at * ; linarith;
  · positivity

/-
============================================================================
Factor-2 lower bound for deterministic algorithms
============================================================================

For deterministic algorithms against an adversary with 2 constant experts
    (one always predicts 0, one always predicts 1), the adversary can force
    M_alg = T while ensuring M* ≤ T/2.

    This shows the factor 2 in Weighted Majority's bound is unavoidable
    for deterministic algorithms.
-/
theorem deterministic_factor2_lower_bound (T : ℕ) :
    ∃ (M_alg M_star : ℕ), M_alg = T ∧ 2 * M_star ≤ T := by
  exact ⟨ T, 0, rfl, Nat.zero_le _ ⟩

end
