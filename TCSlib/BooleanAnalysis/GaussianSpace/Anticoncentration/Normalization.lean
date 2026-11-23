/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.MvPolynomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Transferring normalized polynomial small-ball bounds to intervals

## Main definitions

No new definitions.

## Main results

* `measure_map_Ioc_le_of_normalized_smallBall_bound`: a normalized
  polynomial small-ball bound controls an interval whenever the
  polynomial's square moment about its left endpoint is at least one.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge
  University Press, 2014; May 2021 arXiv edition, §11.6, proof of
  Theorem 11.71.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- A normalized polynomial small-ball bound under a probability measure
controls an interval of width `w` for any polynomial whose second moment
about the interval's left endpoint is at least one.

This is the normalization and interval-containment step used with
Carbery–Wright in [OD14, §11.6, proof of Theorem 11.71].
The normalized bound is an explicit input, so this lemma can be imported
before the Gaussian Carbery–Wright theorem without an import cycle.
No separate integrability assumption is needed: the positive real
shifted-square integral already forces its integrability.

**Proof sketch.** Let `σ` be the square root of the shifted second
moment. It satisfies `σ≥1`. Subtract the left endpoint from the
polynomial and divide by `σ`, preserving the degree bound and giving
square integral one. Every point in the original interval has shifted
absolute value at most `w`, hence normalized absolute value at most
`w`. Apply the assumed small-ball bound at that same positive width
and use monotonicity of the finite measure. -/
theorem measure_map_Ioc_le_of_normalized_smallBall_bound
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (k : ℕ) (K : ℝ)
    (hCW : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ k →
      (∫ x : Fin n → ℝ, (MvPolynomial.eval x q) ^ 2 ∂μ) = 1 →
      ∀ δ : ℝ, 0 < δ →
        (μ {x : Fin n → ℝ | |MvPolynomial.eval x q| ≤ δ}).toReal ≤
          K * (k : ℝ) * δ ^ (1 / (k : ℝ)))
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ k)
    (u : ℝ)
    (hlower :
      1 ≤ ∫ x : Fin n → ℝ, (MvPolynomial.eval x p - u) ^ 2 ∂μ)
    (w : ℝ) (hw : 0 < w) :
    ((μ.map (fun x : Fin n → ℝ => MvPolynomial.eval x p))
      (Set.Ioc u (u + w))).toReal ≤
        K * (k : ℝ) * w ^ (1 / (k : ℝ)) :=
  (by
    let M : ℝ := ∫ x : Fin n → ℝ, (MvPolynomial.eval x p - u) ^ 2 ∂μ
    let σ := Real.sqrt M
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one hlower
    have hσ : 1 ≤ σ := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlower
    have hσpos : 0 < σ := zero_lt_one.trans_le hσ
    have hσsq : σ ^ 2 = M := Real.sq_sqrt hM.le
    let q : MvPolynomial (Fin n) ℝ :=
      MvPolynomial.C σ⁻¹ * p + MvPolynomial.C (-u / σ)
    have hq : q.totalDegree ≤ k := by
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact hp
      · rw [MvPolynomial.totalDegree_C]
        exact Nat.zero_le k
    have heval (x : Fin n → ℝ) : MvPolynomial.eval x q = (MvPolynomial.eval x p - u) / σ := by
      dsimp only [q]
      rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_C]
      ring
    have hnorm : (∫ x : Fin n → ℝ, (MvPolynomial.eval x q) ^ 2 ∂μ) = 1 := by
      simp_rw [heval, div_pow]
      rw [integral_div]
      change M / σ ^ 2 = 1
      rw [hσsq]
      exact div_self hM.ne'
    rw [Measure.map_apply (MvPolynomial.continuous_eval p).measurable measurableSet_Ioc]
    apply (ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono ?_)).trans (hCW q hq hnorm w hw)
    intro x hx
    change u < MvPolynomial.eval x p ∧ MvPolynomial.eval x p ≤ u + w at hx
    change |MvPolynomial.eval x q| ≤ w
    rw [heval, abs_div, abs_of_pos hσpos,
      abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
    exact (div_le_iff₀ hσpos).mpr (by nlinarith [hx.2])

)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
