/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.General

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Applications of finite-product hypercontractivity: statement skeletons

## Main definitions

`productNormComparisonConstant` is defined in `Parameters`, with its continuous value
`e` at `lam = 1/2`.

## Main results

* Theorems 10.21–10.26: low-degree norms, concentration, one-sided anticoncentration,
  small-set expansion, and stable influences.
* The KKL and Friedgut junta results for general product spaces from §10.3.

The product bundle permits heterogeneous coordinates; the homogeneous product statements
in the source follow by choosing the same law at every coordinate. The fourth-exponent
stable-influence corollary applies the general result; the remaining proofs are obligations.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §10.3, Theorems 10.21–10.26 and the named KKL and junta theorems.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

universe u

/-- A degree-`k` product function has `q`-norm at most
`(√(q-1) lam^(1/q-1/2))^k` times its `2`-norm. [OD14, Thm. 10.21]

**Proof sketch.** Rescale each orthogonal component by the inverse noise multiplier,
apply general hypercontractivity, and use orthogonality and the degree cutoff. -/
theorem product_lowDegree_norm {n k : ℕ} (P : FiniteProduct.{u} n)
    (lam q : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam) (hq : 2 < q)
    (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) :
    P.norm q f ≤ (Real.sqrt (q - 1) * lam ^ (1 / q - 1 / 2)) ^ k * P.norm 2 f := sorry

/-- A degree-`k` product function satisfies the sharp limiting `L¹`-to-`L²` comparison.
[OD14, Thm. 10.22] The atom bound is taken at most `1/2`; this is automatic when a
coordinate has at least two outcomes, and a smaller bound can always be chosen.

**Proof sketch.** Interpolate `L¹` with the sharp `L^(2+η)` estimate from Theorem 10.18.
Cancel the `L²` factor and take the limit as `η` decreases to zero. -/
theorem product_lowDegree_l1_l2 {n k : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) :
    P.norm 2 f ≤ productNormComparisonConstant lam ^ k * P.norm 1 f := sorry

/-- The constant in Theorem 10.22 is at most `e/√(2lam)` throughout its range.
[OD14, Thm. 10.22]

**Proof sketch.** Take logarithms of the explicit formula and bound the resulting
logarithmic quotient; at `1/2` use its continuous extension. -/
theorem productNormComparisonConstant_le (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) :
    productNormComparisonConstant lam ≤ Real.exp 1 / Real.sqrt (2 * lam) := sorry

/-- A nonconstant degree-`k` product function exceeds its mean with probability at least
`(e²/(2lam))^(-k)/4`, which is at least `(15/lam)^(-k)`. [OD14, Thm. 10.23]
Positive variance expresses nonconstancy under the full-support product measure.

**Proof sketch.** Center the function. Bound the expectation of its positive part using
the `L¹`-to-`L²` inequality, and then use Cauchy–Schwarz on its positive support. -/
theorem product_oneSided_anticoncentration {n k : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hdeg : P.HasDegreeLE k f) (hf : 0 < P.variance f) :
    (1 / 4 : ℝ) * (Real.exp 2 / (2 * lam)) ^ (-(k : ℝ)) ≤
      P.prob (fun x => P.expect f < f x) ∧
    (15 / lam) ^ (-(k : ℝ)) ≤ (1 / 4 : ℝ) * (Real.exp 2 / (2 * lam)) ^ (-(k : ℝ)) := sorry

/-- A nonzero degree-`k` product function has tail at most
`lam^k exp(-k lam t^(2/k)/(2e))` above `t` times its `2`-norm. [OD14, Thm. 10.24]
The explicit `k > 0` and nonzero norm assumptions resolve the reciprocal-degree and
zero-function boundary cases in the source's non-strict tail event.

**Proof sketch.** Apply Markov's inequality with the `q`-moment bound and choose
`q = lam t^(2/k)/e`; the lower bound on `t` makes this exponent at least two. -/
theorem product_lowDegree_concentration {n k : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hk : 0 < k) (hdeg : P.HasDegreeLE k f)
    (hf : 0 < P.norm 2 f) (t : ℝ) (ht : Real.sqrt (2 * Real.exp 1 / lam) ^ k ≤ t) :
    P.prob (fun x => t * P.norm 2 f ≤ |f x|) ≤
      lam ^ k * Real.exp (-(k : ℝ) / (2 * Real.exp 1) * lam * t ^ (2 / (k : ℝ))) := sorry

/-- The noise stability of an indicator is at most its volume to the power `2-2/q`
at the squared minimum-atom radius. [OD14, Thm. 10.25]

**Proof sketch.** Express stability as the squared `L²` norm after noise at `√ρ`, apply
the conjugate hypercontractive bound, and evaluate the norm of the indicator. -/
theorem product_smallSet_expansion {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 ≤ q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ (1 / (q - 1)) * lam ^ (1 - 2 / q))
    (A : P.Point → Prop) :
    P.stability ρ (P.indicator A) ≤ P.prob A ^ (2 - 2 / q) := sorry

/-- Stable influence, multiplied by `ρ`, is bounded by ordinary influence to the power
`2-2/q` on a finite product. [OD14, Thm. 10.26]

**Proof sketch.** Apply conjugate hypercontractivity to the coordinate Laplacian. The
Boolean range bounds its `q'`-moment by its expected conditional variance, giving the
ordinary influence on the right. -/
theorem product_stableInfluence {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (hq : 2 ≤ q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ (1 / (q - 1)) * lam ^ (1 - 2 / q))
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (i : Fin n) :
    ρ * P.stableInfluence ρ i f ≤ P.influence i f ^ (2 - 2 / q) := sorry

/-- At `q=4`, the weighted spectral influence is at most the ordinary influence to
the power `3/2`. [OD14, Thm. 10.26, equation (10.6)]

**Proof sketch.** Substitute `q=4` and `ρ=√lam/3` in the stable influence estimate and
expand the orthogonal-component formula. -/
theorem product_stableInfluence_four {n : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (i : Fin n) :
    (∑ S : Finset (Fin n), if i ∈ S then (Real.sqrt lam / 3) ^ S.card *
      P.expect (fun x => P.component S f x ^ 2) else 0) ≤
      P.influence i f ^ (3 / 2 : ℝ) := by
  let ρ : ℝ := Real.sqrt lam / 3
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hbound : ρ ≤ (1 / ((4 : ℝ) - 1)) * lam ^ (1 - 2 / (4 : ℝ)) := by
    norm_num [ρ, Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm]
  have h := product_stableInfluence P lam 4 ρ hlam hlam1 hπ
    (by norm_num) hρ hbound f hf i
  norm_num at h
  change (∑ S : Finset (Fin n), if i ∈ S then
    ρ ^ S.card * P.expect (fun x => P.component S f x ^ 2) else 0) ≤
    P.influence i f ^ (3 / 2 : ℝ)
  calc
    _ = ρ * P.stableInfluence ρ i f := by
      rw [FiniteProduct.stableInfluence, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hi : i ∈ S
      · simp only [hi, if_pos]
        have hcard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨i, hi⟩
        rw [← mul_assoc, mul_comm ρ (ρ ^ (S.card - 1)),
          ← pow_succ, Nat.sub_add_cancel hcard]
      · simp [hi]
    _ ≤ _ := h

/-- A nonconstant Boolean product function has a coordinate influence at least
`Ĩ⁻² (9/lam)^(-Ĩ)`, where `Ĩ` is total influence divided by variance.
[OD14, §10.3, KKL Isoperimetric Theorem for general product space domains]

**Proof sketch.** Sum equation (10.6) over coordinates. Normalize nonempty component
weights by the variance and use Jensen's inequality on the exponential of their degrees. -/
theorem product_kkl_isoperimetric {n : ℕ} (P : FiniteProduct.{u} n)
    (lam : ℝ) (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2) (hπ : P.AtomBound lam)
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (hvar : 0 < P.variance f) :
    ∃ i : Fin n, (P.totalInfluence f / P.variance f)⁻¹ ^ 2 *
      (9 / lam) ^ (-(P.totalInfluence f / P.variance f)) ≤ P.influence i f := sorry

/-- The KKL influence lower bound on products loses only a factor `log(1/lam)` compared
with the uniform cube. The constant is independent of every product parameter.
[OD14, §10.3, KKL Isoperimetric Theorem, consequence]

**Proof sketch.** If normalized total influence is large, use the average influence;
otherwise use the exponential isoperimetric estimate to find a larger coordinate. -/
theorem product_kkl : ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (P : FiniteProduct.{u} n) (lam : ℝ), 2 ≤ n → 0 < lam → lam ≤ 1 / 2 →
      P.AtomBound lam → ∀ f : P.Point → ℝ, P.IsBoolean f →
      ∃ i : Fin n, c / Real.log (1 / lam) * P.variance f *
        (Real.log (n : ℝ) / n) ≤ P.influence i f := sorry

/-- Every Boolean product function is `ε`-close to a Boolean junta on at most
`(1/lam)^(C I[f]/ε)` coordinates for an absolute constant `C`.
[OD14, §10.3, Friedgut's Junta Theorem for general product space domains]

**Proof sketch.** Discard high-degree components using total influence and Markov's
inequality. The stable-influence estimate removes low-degree components involving small
influences. Average over the remaining coordinates and round to a Boolean function. -/
theorem product_friedgut_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (P : FiniteProduct.{u} n) (lam : ℝ), 0 < lam → lam ≤ 1 / 2 →
      P.AtomBound lam → ∀ (f : P.Point → ℝ), P.IsBoolean f →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (J : Finset (Fin n)) (g : P.Point → ℝ), P.IsBoolean g ∧ P.DependsOn J g ∧
        (J.card : ℝ) ≤ (1 / lam) ^ (C * P.totalInfluence f / ε) ∧
        P.prob (fun x => f x ≠ g x) ≤ ε := sorry

/-- The sharp comparison constant is asymptotic to `1/√lam` as `lam` decreases to zero.
The limit of the ratio expresses the source's asymptotic equivalence. [OD14, Thm. 10.22]

**Proof sketch.** Take logarithms of the ratio and simplify; the remaining terms tend to
zero using `lam log(lam) → 0`. Exponentiate. -/
theorem productNormComparisonConstant_asymptotic_zero :
    Filter.Tendsto (fun lam : ℝ => productNormComparisonConstant lam * Real.sqrt lam)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := sorry

/-- The sharp comparison constant tends to `e` as the minimum atom mass tends to one half
from below. [OD14, Thm. 10.22]

**Proof sketch.** Take logarithms and evaluate the removable singularity of
`log((1-lam)/lam)/(2(1-2lam))` at one half by differentiation. Exponentiate its limit one. -/
theorem productNormComparisonConstant_tendsto_half :
    Filter.Tendsto productNormComparisonConstant
      (nhdsWithin (1 / 2) (Set.Ioo 0 (1 / 2))) (nhds (Real.exp 1)) := sorry

/-- Small-set expansion also holds up to the square of the sharp discrete radius.
[OD14, Thm. 10.25, parenthetical improvement]

**Proof sketch.** Express stability as the noisy second norm squared, use sharp product
hypercontractivity at `√ρ`, and evaluate the indicator's conjugate norm. -/
theorem product_smallSet_expansion_sharp {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ sharpDiscreteRadius q lam ^ 2)
    (A : P.Point → Prop) :
    P.stability ρ (P.indicator A) ≤ P.prob A ^ (2 - 2 / q) := sorry

/-- Stable influence has the same bound at the squared sharp discrete radius as at the
simpler radius. [OD14, Thm. 10.26, in the full setting of Thm. 10.25]

**Proof sketch.** Apply sharp conjugate hypercontractivity to the coordinate Laplacian
and bound its conjugate moment by the conditional-variance influence. -/
theorem product_stableInfluence_sharp {n : ℕ} (P : FiniteProduct.{u} n)
    (lam q ρ : ℝ) (hlam : 0 < lam) (hlamhalf : lam < 1 / 2) (hπ : P.AtomBound lam)
    (hq : 2 < q) (hρ : 0 ≤ ρ) (hbound : ρ ≤ sharpDiscreteRadius q lam ^ 2)
    (f : P.Point → ℝ) (hf : P.IsBoolean f) (i : Fin n) :
    ρ * P.stableInfluence ρ i f ≤ P.influence i f ^ (2 - 2 / q) := sorry

end BooleanAnalysis.Hypercontractivity
