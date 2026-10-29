/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.HermiteDefinitions
import Mathlib.Algebra.MvPolynomial.Equiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Elementary normalized Hermite identities

## Main definitions

The normalized scalar polynomials and their multivariate products are reused
from `HermiteDefinitions`.

## Main results

* `normalizedHermitePolynomial_zero`, `normalizedHermitePolynomial_one`: the first polynomials.
* `hermiteFunction_eq_prod`: evaluation factors across coordinates.
* `hermiteFunction_zero`: the constant Hermite function.
* `hermiteFunction_indicator`: squarefree monomials are indicator-index Hermites.
* `derivative_hermite_succ`: the scalar Hermite lowering identity.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Definitions 11.29 and 11.32.
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

variable {n : ℕ}

/-- The normalized Hermite polynomial of degree zero is the constant one.
[OD14, Def. 11.29] -/
@[simp] theorem normalizedHermitePolynomial_zero :
    normalizedHermitePolynomial 0 = 1 := by
  simp [normalizedHermitePolynomial, Polynomial.hermite_zero]

/-- The normalized Hermite polynomial of degree one is the coordinate polynomial.
[OD14, Def. 11.29] -/
@[simp] theorem normalizedHermitePolynomial_one :
    normalizedHermitePolynomial 1 = Polynomial.X := by
  simp [normalizedHermitePolynomial]

/-- A multivariate Hermite function is the product of the scalar normalized
Hermite factors evaluated at their respective coordinates. [OD14, Def. 11.32]

**Proof sketch.** Evaluation preserves the finite product. Evaluating a scalar
polynomial inserted into a coordinate evaluates it at that coordinate. -/
theorem hermiteFunction_eq_prod (α : Fin n → ℕ) (x : Fin n → ℝ) :
    hermiteFunction α x =
      ∏ i, (normalizedHermitePolynomial (α i)).eval (x i) := by
  change MvPolynomial.eval x
    (∏ i, (normalizedHermitePolynomial (α i)).toMvPolynomial i) = _
  simp only [map_prod, MvPolynomial.eval_toMvPolynomial]

/-- The Hermite function with every index zero is the constant one.
[OD14, Def. 11.32] -/
@[simp] theorem hermiteFunction_zero (x : Fin n → ℝ) :
    hermiteFunction (fun _ : Fin n => 0) x = 1 := by
  simp [hermiteFunction_eq_prod]

/-- An indicator multi-index gives the ordinary squarefree monomial.
[OD14, Def. 11.32; Remark 11.35]
**Proof sketch.** The scalar normalized Hermites of degree zero and one are
one and the coordinate, so their product is the indicated monomial. -/
theorem hermiteFunction_indicator (S : Finset (Fin n)) (x : Fin n → ℝ) :
    hermiteFunction (fun i => if i ∈ S then 1 else 0) x = ∏ i ∈ S, x i := by
  simp only [hermiteFunction_eq_prod, apply_ite, normalizedHermitePolynomial_zero,
    normalizedHermitePolynomial_one, Polynomial.eval_one, Polynomial.eval_X,
    Fintype.prod_ite_mem]

/-- A subset's indicator index equals `α` exactly when every coordinate of `α`
is zero or one and the subset consists of its coordinates equal to one.
[OD14, Remark 11.35]

**Proof sketch.** Compare coordinates. An indicator takes only the values zero
and one, and its value is one precisely on the given subset. Conversely these
conditions determine every coordinate of the index. -/
lemma indicatorMultiIndex_eq_iff (S : Finset (Fin n)) (α : Fin n → ℕ) :
    (fun i => if i ∈ S then (1 : ℕ) else 0) = α ↔
      (∀ i, α i ≤ 1) ∧ S = Finset.univ.filter (fun i => α i = 1) := by
  classical
  constructor
  · intro h
    subst α
    constructor
    · intro i
      change (if i ∈ S then (1 : ℕ) else 0) ≤ 1
      split_ifs <;> omega
    · ext i
      simp
  · rintro ⟨hα, rfl⟩
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hi
    · exact hi.symm
    · have hle := hα i
      omega

/-- Differentiating a probabilists' Hermite polynomial gives its degree times
the preceding polynomial. [OD14, Def. 11.29]

**Proof sketch.** Differentiate the defining recurrence and use the induction
hypothesis. The recurrence combines the remaining derivative terms into the
preceding Hermite polynomial. -/
lemma derivative_hermite_succ (k : ℕ) :
    (Polynomial.hermite (k + 1)).derivative =
      Polynomial.C ((k + 1 : ℕ) : ℤ) * Polynomial.hermite k := by
  induction k with
  | zero => simp
  | succ k ih =>
    change (Polynomial.hermite ((k + 1) + 1)).derivative =
      Polynomial.C (((k + 1) + 1 : ℕ) : ℤ) * Polynomial.hermite (k + 1)
    rw [Polynomial.hermite_succ]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_X, ih, Polynomial.derivative_C,
      zero_mul, one_mul, zero_add]
    simp only [Polynomial.hermite_succ, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

end BooleanAnalysis.GaussianSpace
