/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exponent arithmetic for Gaussian hypercontractivity

## Main definitions

The extended nonnegative real exponents used by Lp are reused.

## Main results

* `hypercontractive_toReal_condition`: convert the finite-exponent threshold to real arithmetic.
* `hypercontractive_exponents_of_nonzero`: isolate the finite, strictly positive-offset case.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Theorem 11.23.
-/

open scoped ENNReal

namespace BooleanAnalysis.GaussianSpace

/-- For finite exponents at least one, the extended hypercontractivity threshold
is the familiar real inequality. -/
lemma hypercontractive_toReal_condition {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hq : q ≠ ⊤) (ρ : ℝ)
    (hρ : ENNReal.ofReal (ρ ^ 2) * (q - 1) ≤ p - 1) :
    ρ ^ 2 * (q.toReal - 1) ≤ p.toReal - 1 := by
  have hpfin : p ≠ ⊤ := ne_top_of_le_ne_top hq hpq
  have h := ENNReal.toReal_mono (ENNReal.sub_ne_top hpfin) hρ
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg ρ),
    ENNReal.toReal_sub_of_le hp hpfin, ENNReal.toReal_sub_of_le (hp.trans hpq) hq,
    ENNReal.toReal_one] using h

/-- A nonzero correlation that strictly increases the exponent has finite
output exponent and input exponent strictly greater than one.

**Proof sketch.** An infinite output exponent would force an infinite input
exponent. For finite exponents, the positive real threshold rules out input
exponent one when the output exponent is larger. -/
lemma hypercontractive_exponents_of_nonzero {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p < q)
    (ρ : ℝ) (hne : ρ ≠ 0)
    (hρ : ENNReal.ofReal (ρ ^ 2) * (q - 1) ≤ p - 1) : 1 < p ∧ q ≠ ⊤ := by
  have hpfin : p ≠ ⊤ := (lt_of_lt_of_le hpq le_top).ne
  have hqfin : q ≠ ⊤ := by
    intro hqtop
    have hc : ENNReal.ofReal (ρ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hne)).ne'
    have ht : ⊤ ≤ p - 1 := by simpa [hqtop, hc] using hρ
    exact ENNReal.sub_ne_top hpfin (top_le_iff.mp ht)
  have hqreal : 1 < q.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqfin).mpr (hp.trans_lt hpq)
  have hreal := hypercontractive_toReal_condition hp hpq.le hqfin ρ hρ
  have hpreal : 1 < p.toReal := by
    nlinarith [mul_pos (sq_pos_of_ne_zero hne) (sub_pos.mpr hqreal)]
  refine ⟨?_, hqfin⟩
  exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpfin).mp
    (by simpa only [ENNReal.toReal_one] using hpreal)

end BooleanAnalysis.GaussianSpace
