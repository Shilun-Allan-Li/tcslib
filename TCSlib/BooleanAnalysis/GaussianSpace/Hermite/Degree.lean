/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Basic
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Degrees of normalized Hermite polynomials

## Main definitions

The normalized scalar Hermite polynomials and coordinate embeddings are reused.

## Main results

* `normalizedHermitePolynomial_degree`: the scalar degree is its index.
* `totalDegree_toMvPolynomial`: a coordinate embedding preserves degree.
* `totalDegree_finset_prod_of_ne_zero`: total degree is additive over nonzero products.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Definitions 11.29 and 11.32.
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

/-- The normalized Hermite polynomial indexed by `k` has degree `k`.
[OD14, Def. 11.29]

**Proof sketch.** The integer Hermite polynomial is monic of degree `k`.
Mapping to the reals and scaling by a nonzero constant preserve its degree. -/
theorem normalizedHermitePolynomial_degree (k : ℕ) :
    (normalizedHermitePolynomial k).degree = (k : WithBot ℕ) := by
  have hf : (0 : ℝ) < k.factorial := by
    exact_mod_cast Nat.factorial_pos k
  have hs : (Real.sqrt (k.factorial : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hf))
  unfold normalizedHermitePolynomial
  rw [Polynomial.degree_C_mul hs,
    Polynomial.degree_map_eq_of_leadingCoeff_ne_zero _ (by simp),
    Polynomial.degree_hermite]

/-- Every normalized Hermite polynomial is nonzero. [OD14, Def. 11.29] -/
theorem normalizedHermitePolynomial_ne_zero (k : ℕ) :
    normalizedHermitePolynomial k ≠ 0 := by
  intro h
  simpa [h] using normalizedHermitePolynomial_degree k

/-- The natural degree of the normalized Hermite polynomial indexed by `k` is `k`.
[OD14, Def. 11.29] -/
@[simp] theorem normalizedHermitePolynomial_natDegree (k : ℕ) :
    (normalizedHermitePolynomial k).natDegree = k := by
  exact Polynomial.natDegree_eq_of_degree_eq_some
    (normalizedHermitePolynomial_degree k)

/-- Inserting a real scalar polynomial into one coordinate preserves its natural
degree as multivariate total degree.

**Proof sketch.** Use Horner induction. Constants have degree zero, adding a
constant preserves positive degree, and multiplying a nonzero polynomial by the
chosen variable increases degree by one. -/
lemma totalDegree_toMvPolynomial {σ : Type*} (i : σ) (p : Polynomial ℝ) :
    (p.toMvPolynomial i).totalDegree = p.natDegree := by
  have hne (q : Polynomial ℝ) (hq : q ≠ 0) : q.toMvPolynomial i ≠ 0 := by
    intro h
    apply hq
    apply Polynomial.toMvPolynomial_injective i
    simpa using h
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · simp
  · intro q a _ _ ih
    rw [map_add, Polynomial.toMvPolynomial_C, Polynomial.natDegree_add_C]
    by_cases hq : q.natDegree = 0
    · rw [hq]
      apply Nat.eq_zero_of_le_zero
      calc
        (q.toMvPolynomial i + MvPolynomial.C a).totalDegree ≤
            max (q.toMvPolynomial i).totalDegree (MvPolynomial.C a).totalDegree :=
          MvPolynomial.totalDegree_add _ _
        _ = 0 := by simp [ih, hq]
    · exact (MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt
        (by simpa only [MvPolynomial.totalDegree_C, ih] using Nat.pos_of_ne_zero hq)).trans ih
  · intro q hq ih
    rw [map_mul, Polynomial.toMvPolynomial_X,
      MvPolynomial.totalDegree_mul_of_isDomain (hne q hq) (MvPolynomial.X_ne_zero i),
      ih, MvPolynomial.totalDegree_X, Polynomial.natDegree_mul_X hq]

/-- The total degree of a finite product of nonzero real multivariate polynomials
is the sum of their total degrees.

**Proof sketch.** Induct on the finite set and apply additivity of total degree
for a product of two nonzero polynomials. -/
lemma totalDegree_finset_prod_of_ne_zero {σ ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) (hP : ∀ i ∈ s, P i ≠ 0) :
    (∏ i ∈ s, P i).totalDegree = ∑ i ∈ s, (P i).totalDegree := by
  classical
  revert hP
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih hP
    have hs : ∀ i ∈ s, P i ≠ 0 := fun i hi =>
      hP i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      MvPolynomial.totalDegree_mul_of_isDomain
        (hP a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr hs),
      ih hs]

variable {n : ℕ}

/-- The product Hermite polynomial has total degree the sum of its indices.
[OD14, Def. 11.32] **Proof sketch.** Multiply the nonzero leading terms of the
scalar Hermites in their distinct coordinate variables. -/
theorem multivariateHermitePolynomial_totalDegree (α : Fin n → ℕ) :
    (multivariateHermitePolynomial α).totalDegree = ∑ i, α i := by
  change (∏ i, (normalizedHermitePolynomial (α i)).toMvPolynomial i).totalDegree = _
  rw [totalDegree_finset_prod_of_ne_zero]
  · simp only [totalDegree_toMvPolynomial, normalizedHermitePolynomial_natDegree]
  · intro i _ h
    apply normalizedHermitePolynomial_ne_zero (α i)
    apply Polynomial.toMvPolynomial_injective i
    simpa using h

end BooleanAnalysis.GaussianSpace
