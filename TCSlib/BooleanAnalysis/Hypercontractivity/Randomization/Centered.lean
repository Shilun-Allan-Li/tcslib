/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import Mathlib.Analysis.MeanInequalitiesPow
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Estimates for centered negative contraction

## Main definitions

The scalar estimates use absolute real powers and the existing random-variable norms.

## Main results

* `CenteredContraction.remainder_lower`: a quadratic lower bound for the remainder
  after subtracting the constant and linear terms of an absolute power.
* `CenteredContraction.scalar_contraction`: a uniform scalar comparison, with `c = 2/5`
  at exponent four.
* `CenteredContraction.norm_le_of_scalar`: contraction for centered variables from
  the scalar comparison.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §10.4, Lemma 10.43 and Exercise 10.13.
-/

namespace BooleanAnalysis.Hypercontractivity.CenteredContraction

open MeasureTheory

/-- For every exponent `q ≥ 2`, subtracting the constant and linear terms from
`|1 + x| ^ q` leaves a remainder at least `x²`. [OD14, Ex. 10.13(f)]
The inequality includes `x = 0` and `q = 2`.

**Proof sketch.** Apply Bernoulli's inequality with exponent `q/2` to
`(1 + x)² - 1`. The resulting lower bound is `1 + qx + (q/2)x²`,
and `q/2 ≥ 1` gives the claimed quadratic remainder. -/
theorem remainder_lower (q : ℝ) (hq : 2 ≤ q) (x : ℝ) :
    x ^ 2 ≤ |1 + x| ^ q - 1 - q * x := (by
  have hhalf : 1 ≤ q / 2 := by linarith
  have hbern := one_add_mul_self_le_rpow_one_add
    (s := (1 + x) ^ 2 - 1) (by nlinarith [sq_nonneg (1 + x)]) hhalf
  have hpow : ((1 + x) ^ 2) ^ (q / 2) = |1 + x| ^ q := by
    rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg (1 + x))]
    congr 1
    ring
  rw [show 1 + ((1 + x) ^ 2 - 1) = (1 + x) ^ 2 by ring, hpow] at hbern
  nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) (sq_nonneg x)]
)

/-- For `|x| ≤ 1`, the remainder after subtracting the constant and linear terms
from `(1 + x)^m` is at most `(2^m - 1 - m)x²`.
This auxiliary integer-exponent estimate supplies the upper remainder control in
[OD14, Ex. 10.13(b)–(f)].

**Proof sketch.** Induct on the exponent. The next remainder is the current
remainder multiplied by `1 + x`, plus `mx²`. On the given interval,
`0 ≤ 1 + x ≤ 2`. Bernoulli's inequality makes the bound coefficient nonnegative,
and its recurrence is `Kₘ₊₁ = 2Kₘ + m`. -/
theorem pow_remainder_bound (m : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    (1 + x) ^ m - 1 - (m : ℝ) * x ≤
      ((2 : ℝ) ^ m - 1 - (m : ℝ)) * x ^ 2 := (by
  have hx0 : 0 ≤ 1 + x := by linarith [(abs_le.mp hx).1]
  have hx2 : 1 + x ≤ 2 := by linarith [(abs_le.mp hx).2]
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hK : 0 ≤ (2 : ℝ) ^ m - 1 - (m : ℝ) := by
        have h := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) m
        norm_num at h
        linarith
      calc
        (1 + x) ^ (m + 1) - 1 - ((m + 1 : ℕ) : ℝ) * x =
            (1 + x) * ((1 + x) ^ m - 1 - (m : ℝ) * x) + (m : ℝ) * x ^ 2 := by
          rw [pow_succ, Nat.cast_add, Nat.cast_one]
          ring
        _ ≤ (1 + x) * (((2 : ℝ) ^ m - 1 - (m : ℝ)) * x ^ 2) +
            (m : ℝ) * x ^ 2 :=
          add_le_add_right (mul_le_mul_of_nonneg_left ih hx0) _
        _ ≤ 2 * (((2 : ℝ) ^ m - 1 - (m : ℝ)) * x ^ 2) + (m : ℝ) * x ^ 2 :=
          add_le_add_right
            (mul_le_mul_of_nonneg_right hx2 (mul_nonneg hK (sq_nonneg x))) _
        _ = ((2 : ℝ) ^ (m + 1) - 1 - ((m + 1 : ℕ) : ℝ)) * x ^ 2 := by
          rw [pow_succ, Nat.cast_add, Nat.cast_one]
          ring
)

/-- For `q ≥ 2` and any natural exponent `m ≥ q`, the remainder of `|1 + x| ^ q`
after subtracting its constant and linear terms is at most `2^m x²` on `|x| ≤ 1`.
[OD14, Ex. 10.13(c)–(e)]
This explicit estimate replaces the source's local continuity argument.

**Proof sketch.** Set `r = q/m`, which lies in `(0, 1]`. Concave Bernoulli bounds
the real power by `1 + r((1 + x)^m - 1)`. The integer remainder estimate then
applies, and its coefficient multiplied by `r ≤ 1` is at most `2^m`. -/
theorem remainder_local_upper (q : ℝ) (hq : 2 ≤ q) (m : ℕ)
    (hm : q ≤ (m : ℝ)) (x : ℝ) (hx : |x| ≤ 1) :
    |1 + x| ^ q - 1 - q * x ≤
      (2 : ℝ) ^ m * x ^ 2 := (by
  have hm0 : 0 < (m : ℝ) := by linarith
  have hx0 : 0 ≤ 1 + x := by linarith [(abs_le.mp hx).1]
  have hr0 : 0 ≤ q / (m : ℝ) := div_nonneg (by linarith) hm0.le
  have hr1 : q / (m : ℝ) ≤ 1 := div_le_one_of_le₀ hm hm0.le
  have hbern := rpow_one_add_le_one_add_mul_self
    (s := (1 + x) ^ m - 1) (by nlinarith [pow_nonneg hx0 m]) hr0 hr1
  rw [show 1 + ((1 + x) ^ m - 1) = (1 + x) ^ m by ring,
    ← Real.rpow_natCast_mul hx0, mul_div_cancel₀ q hm0.ne'] at hbern
  have hweak : (1 + x) ^ m - 1 - (m : ℝ) * x ≤ (2 : ℝ) ^ m * x ^ 2 :=
    (pow_remainder_bound m x hx).trans
      (mul_le_mul_of_nonneg_right
        (show (2 : ℝ) ^ m - 1 - (m : ℝ) ≤ (2 : ℝ) ^ m by
          linarith [show 0 ≤ (m : ℝ) from Nat.cast_nonneg m])
        (sq_nonneg x))
  rw [abs_of_nonneg hx0]
  calc
    (1 + x) ^ q - 1 - q * x ≤
        (q / (m : ℝ)) * ((1 + x) ^ m - 1 - (m : ℝ) * x) := by
      rw [mul_sub, ← mul_assoc, div_mul_cancel₀ q hm0.ne']
      linarith
    _ ≤ (q / (m : ℝ)) * ((2 : ℝ) ^ m * x ^ 2) :=
      mul_le_mul_of_nonneg_left hweak hr0
    _ ≤ (2 : ℝ) ^ m * x ^ 2 :=
      mul_le_of_le_one_left (mul_nonneg (by positivity) (sq_nonneg x)) hr1
)

/-- For every `q ≥ 2`, the remainder of `|1 + x| ^ q` after subtracting its
constant and linear terms is bounded above by a positive constant times
`x² + |x| ^ q`, uniformly in `x`. [OD14, Ex. 10.13(d)–(e)]
This elementary growth estimate replaces the source's asymptotic and local
continuity estimates.

**Proof sketch.** Choose a natural exponent above `q`. On `|x| ≤ 1`, use the
local quadratic remainder bound. Outside this interval, the triangle inequality
gives `|1 + x| ≤ 2|x|`, and `|x| ≤ |x| ^ q` absorbs the linear term.
A positive constant larger than both coefficients bounds both regions. -/
theorem remainder_upper (q : ℝ) (hq : 2 ≤ q) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
      |1 + x| ^ q - 1 - q * x ≤
        M * (x ^ 2 + |x| ^ q) := (by
  obtain ⟨m, hm⟩ := exists_nat_gt q
  have hq0 : 0 ≤ q := by linarith
  let M : ℝ := (2 : ℝ) ^ m + (2 : ℝ) ^ q + q + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro x
  have hp0 : 0 ≤ |x| ^ q := Real.rpow_nonneg (abs_nonneg x) q
  by_cases hx : |x| ≤ 1
  · calc
      |1 + x| ^ q - 1 - q * x ≤ (2 : ℝ) ^ m * x ^ 2 :=
        remainder_local_upper q hq m hm.le x hx
      _ ≤ M * x ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
        dsimp [M]
        linarith [Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) q]
      _ ≤ M * (x ^ 2 + |x| ^ q) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hp0) hM.le
  · have hlarge : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hpower : |1 + x| ^ q ≤ (2 : ℝ) ^ q * |x| ^ q := by
      rw [← Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (abs_nonneg x)]
      apply Real.rpow_le_rpow (abs_nonneg (1 + x)) _ hq0
      calc
        |1 + x| ≤ 1 + |x| := by simpa using abs_add_le (1 : ℝ) x
        _ ≤ 2 * |x| := by linarith
    have hscale : |x| ≤ |x| ^ q :=
      Real.self_le_rpow_of_one_le hlarge (by linarith)
    calc
      |1 + x| ^ q - 1 - q * x ≤ ((2 : ℝ) ^ q + q) * |x| ^ q := by
        nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs x) hq0,
          mul_le_mul_of_nonneg_left hscale hq0]
      _ ≤ M * |x| ^ q := by
        apply mul_le_mul_of_nonneg_right _ hp0
        dsimp [M]
        linarith [pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) m]
      _ ≤ M * (x ^ 2 + |x| ^ q) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg x)) hM.le
)

/-- For every nonnegative exponent, `|x| ^ q` is at most `2^q` times
`|1 + x| ^ q + 1`. The bound includes `q = 0`.

**Proof sketch.** The triangle inequality gives `|x| ≤ |1 + x| + 1`.
If `|1 + x| ≤ 1`, bound this by two; otherwise, bound it by
`2|1 + x|`. Raise the appropriate bound to the nonnegative exponent. -/
theorem translated_power_bound (q : ℝ) (hq : 0 ≤ q) (x : ℝ) :
    |x| ^ q ≤ (2 : ℝ) ^ q * (|1 + x| ^ q + 1) := (by
  have htri : |x| ≤ |1 + x| + 1 := by
    simpa using abs_add_le (1 + x) (-1 : ℝ)
  have htwo : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) q
  by_cases h : |1 + x| ≤ 1
  · calc
      |x| ^ q ≤ (2 : ℝ) ^ q :=
        Real.rpow_le_rpow (abs_nonneg x) (by linarith) hq
      _ = (2 : ℝ) ^ q * 1 := by ring
      _ ≤ (2 : ℝ) ^ q * (|1 + x| ^ q + 1) :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg (1 + x)) q)) htwo
  · have hlarge : 1 ≤ |1 + x| := (lt_of_not_ge h).le
    calc
      |x| ^ q ≤ (2 * |1 + x|) ^ q :=
        Real.rpow_le_rpow (abs_nonneg x) (by linarith) hq
      _ = (2 : ℝ) ^ q * |1 + x| ^ q :=
        Real.mul_rpow (by norm_num) (abs_nonneg (1 + x))
      _ ≤ (2 : ℝ) ^ q * (|1 + x| ^ q + 1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) htwo
)

/-- For `q ≥ 2`, the remainder of `|1 + x| ^ q` after subtracting its constant
and linear terms controls `|x| ^ q` with factor `2^q(q + 3)`.
[OD14, Ex. 10.13(d)–(f)]
This explicit growth bound replaces the source's asymptotic positivity argument.

**Proof sketch.** On `|x| ≤ 1`, the absolute `q`th power is at most `x²`,
which the remainder dominates. On `|x| ≥ 1`, use the translated-power bound.
Its constant and linear terms are at most `(q + 2)x²`, so the quadratic
remainder bound absorbs them. -/
theorem remainder_power_lower (q : ℝ) (hq : 2 ≤ q) (x : ℝ) :
    |x| ^ q ≤ (2 : ℝ) ^ q * (q + 3) *
      (|1 + x| ^ q - 1 - q * x) := (by
  have hq0 : 0 ≤ q := by linarith
  have htwo : 1 ≤ (2 : ℝ) ^ q := Real.one_le_rpow (by norm_num) hq0
  let R : ℝ := |1 + x| ^ q - 1 - q * x
  have hrem : x ^ 2 ≤ R := remainder_lower q hq x
  change |x| ^ q ≤ (2 : ℝ) ^ q * (q + 3) * R
  by_cases hx : |x| ≤ 1
  · have hB : 1 ≤ (2 : ℝ) ^ q * (q + 3) := by
      calc
        1 ≤ q + 3 := by linarith
        _ ≤ (2 : ℝ) ^ q * (q + 3) :=
          le_mul_of_one_le_left (by linarith) htwo
    calc
      |x| ^ q ≤ x ^ 2 := by
        simpa only [Real.rpow_two, sq_abs] using
          (Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg x) hx
            (by norm_num : 0 ≤ (2 : ℝ)) hq)
      _ ≤ R := hrem
      _ ≤ (2 : ℝ) ^ q * (q + 3) * R :=
        le_mul_of_one_le_left ((sq_nonneg x).trans hrem) hB
  · have hlarge : 1 ≤ |x| := (lt_of_not_ge hx).le
    have habssq : |x| ≤ x ^ 2 := by
      calc
        |x| = |x| * 1 := by ring
        _ ≤ |x| * |x| := mul_le_mul_of_nonneg_left hlarge (abs_nonneg x)
        _ = x ^ 2 := by rw [← pow_two, sq_abs]
    have hsum : |1 + x| ^ q + 1 ≤ (q + 3) * R := by
      have hscale := mul_le_mul_of_nonneg_left hrem
        (show 0 ≤ q + 2 by linarith)
      have hlinear := mul_le_mul_of_nonneg_left
        ((le_abs_self x).trans habssq) hq0
      have hsq : 1 ≤ x ^ 2 := hlarge.trans habssq
      dsimp [R] at hrem hscale ⊢
      nlinarith
    simpa only [mul_assoc] using
      (translated_power_bound q hq0 x).trans
        (mul_le_mul_of_nonneg_left hsum (zero_le_one.trans htwo))
)

/-- For every `q ≥ 2`, some positive coefficient `c ≤ 1` bounds
`|1 - cx| ^ q` by `|1 + x| ^ q - q(1 + c)x` for every real `x`.
[OD14, Ex. 10.13(b)–(f)]
The proof uses elementary remainder bounds instead of the source's continuity argument.

**Proof sketch.** Bound the remainder above by `M(x² + |x| ^ q)` and below
in both degrees. With `B = 2^q(q + 3)`, the reflected remainder is at most
`M(1 + B)c²` times the original remainder, since `c^q ≤ c²`.
Taking `c = 1/(1 + M(1 + B))` makes this multiplier at most one. -/
theorem scalar_contraction_generic (q : ℝ) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ x : ℝ,
      |1 - c * x| ^ q ≤
        |1 + x| ^ q - q * (1 + c) * x := (by
  obtain ⟨M, hM, hupper⟩ := remainder_upper q hq
  have hq0 : 0 ≤ q := by linarith
  let B : ℝ := (2 : ℝ) ^ q * (q + 3)
  let A : ℝ := M * (1 + B)
  let c : ℝ := 1 / (1 + A)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_one (by positivity : 0 < 1 + A)).2
    linarith
  have hcsq : c ^ 2 ≤ c := by
    nlinarith [mul_nonneg hc0.le (sub_nonneg.mpr hc1)]
  have hAc : A * c ≤ 1 := by
    dsimp [c]
    rw [mul_one_div]
    apply (div_le_one (by positivity : 0 < 1 + A)).2
    linarith
  have hAcsq : A * c ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hcsq hA.le).trans hAc
  have hcq : c ^ q ≤ c ^ 2 := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_ge hc0 hc1 hq)
  refine ⟨c, hc0, hc1, ?_⟩
  intro x
  let R : ℝ := |1 + x| ^ q - 1 - q * x
  have hR : 0 ≤ R := (sq_nonneg x).trans (remainder_lower q hq x)
  have hsum : x ^ 2 + |x| ^ q ≤ (1 + B) * R := by
    have hp : |x| ^ q ≤ B * R := remainder_power_lower q hq x
    simpa only [add_mul, one_mul] using add_le_add (remainder_lower q hq x) hp
  have hcontract : |1 + (-(c * x))| ^ q - 1 - q * (-(c * x)) ≤ R := by
    calc
      |1 + (-(c * x))| ^ q - 1 - q * (-(c * x)) ≤
          M * ((-(c * x)) ^ 2 + |-(c * x)| ^ q) := hupper (-(c * x))
      _ = M * (c ^ 2 * x ^ 2 + c ^ q * |x| ^ q) := by
        rw [neg_sq, mul_pow, abs_neg, abs_mul, abs_of_pos hc0,
          Real.mul_rpow hc0.le (abs_nonneg x)]
      _ ≤ M * (c ^ 2 * x ^ 2 + c ^ 2 * |x| ^ q) :=
        mul_le_mul_of_nonneg_left
          (add_le_add_left
            (mul_le_mul_of_nonneg_right hcq (Real.rpow_nonneg (abs_nonneg x) q)) _) hM.le
      _ = M * c ^ 2 * (x ^ 2 + |x| ^ q) := by ring
      _ ≤ M * c ^ 2 * ((1 + B) * R) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hM.le (sq_nonneg c))
      _ = A * c ^ 2 * R := by dsimp [A]; ring
      _ ≤ R := mul_le_of_le_one_left hR hAcsq
  dsimp [R] at hcontract
  rw [← sub_eq_add_neg] at hcontract
  nlinarith
)

/-- For every `q ≥ 2`, some positive coefficient `c ≤ 1` bounds
`|1 - cx| ^ q` by `|1 + x| ^ q - q(1 + c)x` for every real `x`;
at exponent four, one may take `c = 2/5`. [OD14, Lem. 10.43; Ex. 10.13(a)–(f)]

**Proof sketch.** Use the general remainder estimate except at exponent four.
There, take `c = 2/5` and expand the quartic difference. A square bound makes
its quadratic factor nonnegative, leaving positive multiples of `x⁴` and `x²`. -/
theorem scalar_contraction (q : ℝ) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ (q = 4 → c = 2 / 5) ∧
      ∀ x : ℝ, |1 - c * x| ^ q ≤
        |1 + x| ^ q - q * (1 + c) * x := (by
  by_cases hq4 : q = 4
  · subst q
    refine ⟨2 / 5, by norm_num, by norm_num, by simp, ?_⟩
    intro x
    simp only [Real.rpow_ofNat, (show Even (4 : ℕ) from by decide).pow_abs]
    nlinarith [sq_nonneg (x * (4 * x + 9)), sq_nonneg (x ^ 2), sq_nonneg x]
  · obtain ⟨c, hc0, hc1, hc⟩ := scalar_contraction_generic q hq
    exact ⟨c, hc0, hc1, fun h => (hq4 h).elim, hc⟩
)

/-- A normalized reflected-power comparison extends by homogeneity to every
real translate, with linear correction `q(1 + c)|a|^q x/a`.
[OD14, Lem. 10.43, proof]

**Proof sketch.** For a nonzero translate, apply the normalized comparison to
`x/a` and multiply by `|a| ^ q`. Absolute powers factor under this scaling.
For a zero translate, `0 ≤ c ≤ 1` directly bounds the contracted power. -/
theorem scalar_affine (q : ℝ) (hq : 0 < q) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hscalar : ∀ z : ℝ, |1 - c * z| ^ q ≤
      |1 + z| ^ q - q * (1 + c) * z)
    (a x : ℝ) :
    |a - c * x| ^ q ≤
      |a + x| ^ q - (q * (1 + c) * |a| ^ q / a) * x :=
        (by
  by_cases ha : a = 0
  · subst a
    simp only [zero_sub, zero_add, div_zero, zero_mul, sub_zero,
      abs_neg, abs_mul, abs_of_nonneg hc0]
    apply Real.rpow_le_rpow (mul_nonneg hc0 (abs_nonneg x)) _ hq.le
    exact mul_le_of_le_one_left (abs_nonneg x) hc1
  · calc
      |a - c * x| ^ q = |a| ^ q * |1 - c * (x / a)| ^ q := by
        rw [show a - c * x = a * (1 - c * (x / a)) by
          field_simp [ha], abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg _)]
      _ ≤ |a| ^ q * (|1 + x / a| ^ q - q * (1 + c) * (x / a)) :=
        mul_le_mul_of_nonneg_left (hscalar (x / a))
          (Real.rpow_nonneg (abs_nonneg a) q)
      _ = |a + x| ^ q - (q * (1 + c) * |a| ^ q / a) * x := by
        rw [mul_sub, ← Real.mul_rpow (abs_nonneg a) (abs_nonneg _), ← abs_mul,
          show a * (1 + x / a) = a + x by field_simp [ha]]
        ring
)

/-- A normalized scalar comparison at `q ≥ 2` gives negative affine norm
contraction for every centered random variable with finite `q`-norm.
[OD14, Lem. 10.43, proof]

**Proof sketch.** Lift the scalar comparison to the translate `a` by homogeneity.
Integrate it; centering removes the linear correction. Express the absolute
moments as powers of the finite norms, then use monotonicity of the positive
power to compare the norms. -/
theorem norm_le_of_scalar {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℝ) (hq : 2 ≤ q) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hscalar : ∀ z : ℝ, |1 - c * z| ^ q ≤
      |1 + z| ^ q - q * (1 + c) * z)
    (X : Ω → ℝ) (hX : MemLp X (ENNReal.ofReal q) μ)
    (hmean : (∫ ω, X ω ∂μ) = 0) (a : ℝ) :
    rvLpNorm (fun ω => a - c * X ω) μ q ≤
      rvLpNorm (fun ω => a + X ω) μ q := (by
  have hqpos : 0 < q := by linarith
  have hleft : MemLp (fun ω => a - c * X ω) (ENNReal.ofReal q) μ :=
    (memLp_const a).sub (hX.const_mul c)
  have hright : MemLp (fun ω => a + X ω) (ENNReal.ofReal q) μ :=
    (memLp_const a).add hX
  have hIleft : Integrable (fun ω => |a - c * X ω| ^ q) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hqpos.le] using
      hleft.integrable_norm_rpow'
  have hIright : Integrable (fun ω => |a + X ω| ^ q) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hqpos.le] using
      hright.integrable_norm_rpow'
  have hXint : Integrable X μ :=
    MemLp.integrable
      (by simpa using ENNReal.ofReal_le_ofReal (show 1 ≤ q by linarith)) hX
  let b : ℝ := q * (1 + c) * |a| ^ q / a
  apply (Real.rpow_le_rpow_iff
    (show 0 ≤ rvLpNorm (fun ω => a - c * X ω) μ q from ENNReal.toReal_nonneg)
    (show 0 ≤ rvLpNorm (fun ω => a + X ω) μ q from ENNReal.toReal_nonneg)
    hqpos).mp
  rw [rvLpNorm_rpow _ μ q hqpos hleft, rvLpNorm_rpow _ μ q hqpos hright]
  calc
    (∫ ω, |a - c * X ω| ^ q ∂μ) ≤
        ∫ ω, |a + X ω| ^ q - b * X ω ∂μ :=
      integral_mono hIleft (hIright.sub (hXint.const_mul b))
        (fun ω => scalar_affine q hqpos c hc0 hc1 hscalar a (X ω))
    _ = ∫ ω, |a + X ω| ^ q ∂μ := by
      rw [integral_sub hIright (hXint.const_mul b), integral_const_mul,
        hmean, mul_zero, sub_zero]
)

end BooleanAnalysis.Hypercontractivity.CenteredContraction
