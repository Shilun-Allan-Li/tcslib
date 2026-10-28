/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Degree
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Quotient.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Algebraic completeness of Hermite polynomials

## Main definitions

* `normalizedHermiteSequence`: the scalar Hermites as a polynomial sequence.
* `normalizedHermiteBasis`: their algebraic basis of the real polynomial space.

## Main results

* `coordinatePolynomialProduct_mem_span_hermite`: coordinate products lie in the Hermite span.
* `span_multivariateHermitePolynomial_eq_top`: the multivariate Hermites span all polynomials.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Definitions 11.29 and 11.32,
  Propositions 11.30 and 11.33.
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

/-- The normalized Hermites form a polynomial sequence with degree equal to index.
[OD14, Def. 11.29] -/
noncomputable def normalizedHermiteSequence : Polynomial.Sequence ℝ where
  elems' := normalizedHermitePolynomial
  degree_eq' := normalizedHermitePolynomial_degree

/-- The normalized Hermites form an algebraic basis of real scalar polynomials.
[OD14, §11.2, Prop. 11.30]

**Proof sketch.** The degrees enumerate the natural numbers and all leading
coefficients are units, so the polynomial-sequence basis construction applies. -/
noncomputable def normalizedHermiteBasis : Module.Basis ℕ ℝ (Polynomial ℝ) :=
  normalizedHermiteSequence.basis fun k =>
    isUnit_iff_ne_zero.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr (normalizedHermitePolynomial_ne_zero k))

/-- The degree-`k` vector of the scalar Hermite basis is the concrete normalized
degree-`k` Hermite polynomial. [OD14, Def. 11.29] -/
@[simp] theorem normalizedHermiteBasis_apply (k : ℕ) :
    normalizedHermiteBasis k = normalizedHermitePolynomial k := by
  simp [normalizedHermiteBasis, normalizedHermiteSequence]

variable {n : ℕ}

/-- Every coordinate product of scalar polynomials is a finite linear combination
of multivariate Hermite polynomials. [OD14, Def. 11.32; Prop. 11.33]

**Proof sketch.** Compose the coordinate-product multilinear map with the quotient
by the Hermite span. This composite vanishes on tuples of scalar Hermite basis
vectors, so multilinear basis extensionality makes it vanish everywhere. -/
lemma coordinatePolynomialProduct_mem_span_hermite (p : Fin n → Polynomial ℝ) :
    (∏ i, (p i).toMvPolynomial i) ∈
      Submodule.span ℝ (Set.range (@multivariateHermitePolynomial n)) := by
  let N : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
    Submodule.span ℝ (Set.range (@multivariateHermitePolynomial n))
  let F : MultilinearMap ℝ (fun _ : Fin n => Polynomial ℝ) (MvPolynomial (Fin n) ℝ) :=
    (MultilinearMap.mkPiAlgebra ℝ (Fin n) (MvPolynomial (Fin n) ℝ)).compLinearMap
      (fun i => (Polynomial.toMvPolynomial i).toLinearMap)
  have hF : N.mkQ.compMultilinearMap F = 0 := by
    apply Module.Basis.ext_multilinear (fun _ : Fin n => normalizedHermiteBasis)
    intro α
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.zero_apply, F,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      normalizedHermiteBasis_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change multivariateHermitePolynomial α ∈ N
    exact Submodule.subset_span ⟨α, rfl⟩
  have hp := congrArg (fun G => G p) hF
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.zero_apply, F,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hp
  exact hp

/-- Multivariate Hermite polynomials span the entire real multivariate polynomial
space. [OD14, Def. 11.32; Prop. 11.33]

**Proof sketch.** A monomial is a scalar multiple of a coordinate product of
scalar powers. Such products lie in the Hermite span, and polynomials are finite
sums of monomials. -/
theorem span_multivariateHermitePolynomial_eq_top :
    Submodule.span ℝ (Set.range (@multivariateHermitePolynomial n)) = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro P
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
      simpa [map_pow, Polynomial.toMvPolynomial_X,
        MvPolynomial.monomial_eq, Finsupp.prod_fintype,
        Algebra.smul_def] using
        Submodule.smul_mem
          (Submodule.span ℝ (Set.range (@multivariateHermitePolynomial n))) a
          (coordinatePolynomialProduct_mem_span_hermite
            (fun i => (Polynomial.X : Polynomial ℝ) ^ u i))
  | add P Q hP hQ =>
      exact Submodule.add_mem _ hP hQ

end BooleanAnalysis.GaussianSpace
