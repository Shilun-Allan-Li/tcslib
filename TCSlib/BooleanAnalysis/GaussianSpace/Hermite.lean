/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Basic
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Degree
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Orthogonality
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Span
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Basis
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Truncation
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.GeneratingFunction
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Generator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hermite expansions and Gaussian spectral theory

## Main definitions

* `hermiteL2`: the L² class of the concrete normalized Hermite function.
  Its membership obligation is explicitly stated before the adapter.

## Contents

* `Hermite.Basic`: scalar base cases and coordinate-product evaluation identities.
* `Hermite.Degree`: scalar degrees and degree preservation under coordinate embeddings.
* `Hermite.Orthogonality`: polynomial Gaussian integration by parts and scalar orthogonality.
* `Hermite.Span`: algebraic spanning by scalar and multivariate Hermite polynomials.
* `Hermite.Basis`: the Gaussian L² basis, expansions, Plancherel, and variance.
* `Hermite.Truncation`: finite total-degree approximations in Gaussian L².
* `Hermite.Noise`: Gaussian affine Hermite identities and noise spectrum.
* `Hermite.GeneratingFunction`: the scalar exponential generating function.
* `Hermite.Generator`: degree multipliers and the strong Gaussian generator domain.

## Main results

Polynomial degrees, elementary evaluation identities, finite Gaussian moments,
orthonormality, completeness, unique L² expansions, degree truncation, Plancherel,
variance, multilinear coefficients, the generating function, and the Gaussian noise
spectrum are proved. The positive Gaussian generator multiplies coefficients by
total degree; its domain consists exactly of the square-summable weighted spectra.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Propositions 11.30–11.40 and Exercise 11.18.
-/

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}

/-- The existing multilinear coefficients equal Hermite coefficients on
squarefree indices and vanish on all other indices. [OD14, Remark 11.35]

**Proof sketch.** Identify squarefree Hermites with monomials, expand the
existing multilinear evaluation, and apply Hermite orthogonality. -/
theorem hermiteCoeff_multilinear (F : MultilinearPolynomial n) (α : Fin n → ℕ) :
    hermiteCoeff (Hypercontractivity.evalMultilinearRV F (fun i z => z i)) α =
      if ∀ i, α i ≤ 1 then F (Finset.univ.filter fun i => α i = 1) else 0 := by
  classical
  unfold Hypercontractivity.evalMultilinearRV
  simp_rw [← hermiteFunction_indicator]
  rw [hermiteCoeff_finset_sum_hermiteFunction]
  simp_rw [indicatorMultiIndex_eq_iff]
  by_cases h : ∀ i, α i ≤ 1 <;> simp [h]

end BooleanAnalysis.GaussianSpace
