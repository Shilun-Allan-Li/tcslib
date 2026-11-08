/-
Copyright (c) 2026 Arhaan Aggarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arhaan Aggarwal
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Cases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Weighted Majority Algorithm: Mistake Bound

The potential-function argument behind the Weighted Majority mistake bound in the agnostic
setting [MRT18, Thm 8.3]: the total weight of the experts shrinks by a factor `(1+β)/2` at
every mistake of the algorithm, while the best expert's weight `β^{M*}` is a lower bound on
the total weight, so `M_WM · log(2/(1+β)) ≤ log n + M* · log(1/β)`. The algorithm itself is
not modeled: the weight sequence is an abstract function `ℕ → ℝ` and the per-mistake
shrinkage and the best-expert lower bound enter as hypotheses.

## Main definitions

This file contains no definitions; the weight sequences are abstract hypotheses of the
theorems.

## Main results

- `wm_weight_shrinkage`: After M algorithm mistakes, total weight satisfies
  W_M ≤ W₀ · ((1+β)/2)^M
- `wm_weight_upper_bound`: After M algorithm mistakes starting from n unit-weight experts,
  W_M ≤ n · ((1+β)/2)^M
- `wm_combined_potential_bound`: Taking logs of the potential bound
  β^M_star ≤ n · ((1+β)/2)^M_WM
- `wm_mistake_bound_log`: Logarithmic mistake bound
  M_WM · log(2/(1+β)) ≤ log(n) + M_star · log(1/β)

## References

* [MRT18] M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*,
  2nd ed., MIT Press, 2018.
* [LW94] N. Littlestone, M. K. Warmuth, "The Weighted Majority Algorithm",
  *Information and Computation* 108(2):212–261, 1994.

Original formalization by Arhaan Aggarwal.
-/

open Finset BigOperators Real

noncomputable section

/-- Iterated weight shrinkage: if a positive weight sequence `W` satisfies
`W (k+1) ≤ W k · (1+β)/2` for every `k < M`, then `W M ≤ W 0 · ((1+β)/2)^M`.
[MRT18, proof of Thm 8.3] (the step `W_{t+1} ≤ ((1+β)/2) · W_t`); [LW94, §2].

In Weighted Majority, when the algorithm makes a mistake at least half the total weight sits
on the experts that were wrong; those experts are multiplied by `β`, so the new total weight
is at most `(1+β)/2` times the old one. Deviation: that per-mistake shrinkage is taken as
the hypothesis `hW_step` on an abstract weight sequence indexed by mistake count rather than
derived from the algorithm; `β < 1` and positivity of `W` are not used. -/
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

/-- Upper bound on the total weight after `M` mistakes: starting from `n` experts of unit
weight (`W 0 = n`) and shrinking by the factor `(1+β)/2` at each of the first `M` steps,
`W M ≤ n · ((1+β)/2)^M`. [MRT18, proof of Thm 8.3] (`W_T ≤ N · ((1+β)/2)^{M_WM}`);
[LW94, §2]. Deviation: as in `wm_weight_shrinkage`, the shrinkage is the hypothesis
`hW_step` on an abstract weight sequence; the hypotheses `0 < n` and `β < 1` are unused. -/
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

/-- Logarithmic form of the combined potential inequality: given the hypothesis `h_lower`
that `β^{M*} ≤ n · ((1+β)/2)^{M_WM}`, the same inequality holds between the logarithms,
`log(β^{M*}) ≤ log(n · ((1+β)/2)^{M_WM})`. [MRT18, proof of Thm 8.3].

In the source the two sides come from the two halves of the potential argument: the best
expert makes `M*` mistakes, so its final weight `β^{M*}` is at most the total weight `W_T`,
and `W_T ≤ n · ((1+β)/2)^{M_WM}` by `wm_weight_upper_bound`. Deviation: here the combined
inequality is *assumed* as `h_lower` (the best-expert lower bound `β^{M*} ≤ W_T` is not
derived); the theorem only applies monotonicity of the logarithm. -/
theorem wm_combined_potential_bound
    (n : ℕ) (_hn : 0 < n)
    (β : ℝ) (hβ0 : 0 < β) (_hβ1 : β < 1)
    (M_star M_WM : ℕ)
    (h_lower : β ^ M_star ≤ (n : ℝ) * ((1 + β) / 2) ^ M_WM)
    : Real.log (β ^ M_star) ≤ Real.log ((n : ℝ) * ((1 + β) / 2) ^ M_WM) := by
  gcongr

/-- The Weighted Majority mistake bound in logarithmic form: for `n > 1` experts, `0 < β < 1`,
and under the potential hypothesis `h : β^{M*} ≤ n · ((1+β)/2)^{M_WM}`,
`M_WM · log(2/(1+β)) ≤ log n + M* · log(1/β)`; equivalently
`M_WM ≤ (log n + M* · log(1/β)) / log(2/(1+β))`. [MRT18, Thm 8.3]; [LW94, §2].

Deviation: the source derives the potential inequality from the algorithm; here it is the
hypothesis `h`, and the theorem takes logarithms and rearranges (since `log((1+β)/2) < 0`
the inequality is written with `log(2/(1+β)) > 0`). The hypothesis `1 < n` is stronger than
needed: `0 < n` suffices. -/
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

end
