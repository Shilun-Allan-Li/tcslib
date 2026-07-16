import Mathlib

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open Finset BigOperators Real

noncomputable section
lemma mul_one_sub_le_quarter (x : ℝ) (_hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    x * (1 - x) ≤ 1 / 4 := by
  linarith [sq_nonneg (x - 1 / 2)]
end
