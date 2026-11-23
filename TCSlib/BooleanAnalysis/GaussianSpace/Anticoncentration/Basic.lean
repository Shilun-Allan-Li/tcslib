/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Scalar bounds for polynomial anticoncentration

## Main definitions

No new definitions.

## Main results

* `le_exp_mul_degree_mul_rpow_of_sq_le_factorial_bound`: converts a
  squared-norm factorial estimate into a degree-linear small-ball bound.

## References

* [CW01] A. Carbery and J. Wright, *Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn*, Mathematical Research Letters
  8 (2001), 233–248, §4. The result below isolates scalar bookkeeping
  in the explicit coarse-constant Remez estimate.
-/

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- If positive real numbers satisfy the squared-norm factorial bound
with base `16 * exp 2 / m` and degree parameter `d ≥ 1`, then
`m ≤ 32 * exp 3 * d * (ε / a)^(1/d)`.

This is the pure scalar factorial and root comparison used in the
coarse-constant Remez method of [CW01, §4]. It introduces no measure,
polynomial or integrability hypothesis.

**Proof sketch.** Bound `(2d)!` by `(2d)^(2d)`, and bound `exp 1`
by its `2d`-th power. Combining these factors gives
`a² ≤ ε² * ((32 * exp 3 * d) / m)^(2d)`. Clear the positive
denominators. The `2d`-th power of `(ε/a)^(1/d)` is `(ε/a)²`;
monotonicity of this positive even power gives the result. -/
theorem le_exp_mul_degree_mul_rpow_of_sq_le_factorial_bound
    (d : ℕ) (hd : 1 ≤ d)
    (a ε m : ℝ) (ha : 0 < a) (hε : 0 < ε) (hm : 0 < m)
    (hbound :
      a ^ 2 ≤ ε ^ 2 * (16 * Real.exp 2 / m) ^ (2 * d) *
        Real.exp 1 * ((2 * d).factorial : ℝ)) :
    m ≤ 32 * Real.exp 3 * (d : ℝ) *
      (ε / a) ^ (1 / (d : ℝ)) :=
  (by
  have hd0 : d ≠ 0 := by omega
  have hn : 2 * d ≠ 0 := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let C : ℝ := 32 * Real.exp 3 * (d : ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hf : ((2 * d).factorial : ℝ) ≤ ((2 * d : ℕ) : ℝ) ^ (2 * d) := by
    exact_mod_cast Nat.factorial_le_pow (2 * d)
  have he : Real.exp 1 ≤ (Real.exp 1) ^ (2 * d) :=
    le_self_pow₀ (Real.one_le_exp (by norm_num)) hn
  have hcoarse : a ^ 2 ≤ ε ^ 2 * (C / m) ^ (2 * d) := by
    apply hbound.trans
    calc
      _ ≤ ε ^ 2 * (16 * Real.exp 2 / m) ^ (2 * d) *
          (Real.exp 1) ^ (2 * d) * ((2 * d : ℕ) : ℝ) ^ (2 * d) := by
        gcongr
      _ = _ := by
        simp only [mul_assoc]
        rw [← mul_pow, ← mul_pow]
        congr 2
        dsimp only [C]
        push_cast
        rw [show Real.exp 3 = Real.exp 2 * Real.exp 1 by
          rw [← Real.exp_add]; norm_num]
        ring
  have hmul : a ^ 2 * m ^ (2 * d) ≤ ε ^ 2 * C ^ (2 * d) := by
    apply (le_div_iff₀ (pow_pos hm (2 * d))).mp
    calc
      _ ≤ ε ^ 2 * (C / m) ^ (2 * d) := hcoarse
      _ = _ := by rw [div_pow]; ring
  have hroot : ((ε / a) ^ (1 / (d : ℝ))) ^ (2 * d) = (ε / a) ^ 2 := by
    rw [Nat.mul_comm 2 d, pow_mul, one_div,
      Real.rpow_inv_natCast_pow (by positivity) hd0]
  apply (pow_le_pow_iff_left₀ hm.le
    (by positivity : 0 ≤ C * (ε / a) ^ (1 / (d : ℝ))) hn).mp
  rw [mul_pow, hroot]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ha)).mp
  calc
    _ ≤ ε ^ 2 * C ^ (2 * d) := hmul
    _ = _ := by field_simp
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
