/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Algebra.MvPolynomial.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Normalized Gaussian Hermite functions

## Main definitions

* `normalizedHermitePolynomial`: Mathlib's probabilists' polynomial divided by `√k!`.
* `multivariateHermitePolynomial`: the coordinate product as an ordinary multivariate polynomial.
* `hermiteFunction`: its evaluation on the existing real vector carrier.
* `hermiteCoeff`: the Gaussian inner-product coefficient.

## Main results

Definitions only. `Hermite` supplies the analytic statement layer. The unnormalized
Hermite construction is reused from Mathlib; no recurrence is redefined.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Definitions 11.29, 11.32 and 11.34.
-/

open MeasureTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The normalized probabilists' Hermite polynomial `h_k=H_k/√k!`, using
Mathlib's integer-coefficient `Polynomial.hermite`. [OD14, Def. 11.29] -/
noncomputable def normalizedHermitePolynomial (k : ℕ) : Polynomial ℝ :=
  Polynomial.C ((Real.sqrt (k.factorial : ℝ))⁻¹) *
    (Polynomial.hermite k).map (Int.castRingHom ℝ)

/-- The product of normalized scalar Hermite polynomials with multi-index `α`.
This is an arbitrary multivariate polynomial, not a multilinear Walsh expansion.
[OD14, Def. 11.32] -/
noncomputable def multivariateHermitePolynomial {n : ℕ} (α : Fin n → ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i, Polynomial.aeval (MvPolynomial.X i) (normalizedHermitePolynomial (α i))

/-- The normalized multivariate Hermite function on the existing Gaussian vector
carrier. [OD14, Def. 11.32] -/
noncomputable def hermiteFunction {n : ℕ} (α : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval x (multivariateHermitePolynomial α)

/-- The coefficient of a Gaussian L² function at a normalized Hermite function.
[OD14, Def. 11.34] Results impose L² hypotheses so this inner product is integrable. -/
noncomputable def hermiteCoeff {n : ℕ} (f : (Fin n → ℝ) → ℝ) (α : Fin n → ℕ) : ℝ :=
  ∫ x, f x * hermiteFunction α x
    ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)

end BooleanAnalysis.GaussianSpace
