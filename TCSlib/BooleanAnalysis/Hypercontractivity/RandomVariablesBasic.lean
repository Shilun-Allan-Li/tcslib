/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.Parameters
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.MomentBounds
import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Definitions for hypercontractivity of general random variables

## Main definitions

* `IsHypercontractive`: affine norm contraction, including infinite exponents.
* `IsSymmetricRV`, `IsRademacherRV`: symmetry and the uniform sign law.
* `evalMultilinearRV`: evaluate existing multilinear polynomials on real random inputs.
* `HasAtomLowerBound`, `sharpDiscreteRadius`: discrete laws and their sharp noise radius.

## Main results

This file contains definitions. The corresponding statement skeletons are in `RandomVariables`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Corollary 9.6, Definition 9.13, and §10.2.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.Hypercontractivity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random variable is `(p,q,ρ)`-hypercontractive when every affine perturbation contracts
from its finite `p`-norm to its `q`-norm after scaling the nonconstant part by `ρ`.
Extended nonnegative exponents include infinity. [OD14, Def. 9.13] -/
def IsHypercontractive (X : Ω → ℝ) (μ : Measure Ω) (p q : ℝ≥0∞) (ρ : ℝ) : Prop :=
  1 ≤ p ∧ p ≤ q ∧ 0 ≤ ρ ∧ ρ < 1 ∧ MemLp X q μ ∧
    ∀ a b : ℝ, eLpNorm (fun ω => a + ρ * b * X ω) q μ ≤
      eLpNorm (fun ω => a + b * X ω) p μ

/-- The real-valued `q`-norm is used with finite-norm hypotheses to avoid totalizing
an infinite norm to zero. [OD14, §10.2] -/
noncomputable def rvLpNorm (X : Ω → ℝ) (μ : Measure Ω) (q : ℝ) : ℝ :=
  (eLpNorm X (ENNReal.ofReal q) μ).toReal

/-- A symmetric variable has the same distribution as its negative.
[OD14, §10.2, preceding Prop. 10.12] -/
def IsSymmetricRV (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  IdentDistrib X (fun ω => -X ω) μ μ

/-- A Rademacher variable is a measurable uniform random sign.
[OD14, §10.2, randomization preceding Thm. 10.13] -/
def IsRademacherRV (r : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Measurable r ∧ (∀ᵐ ω ∂μ, r ω = -1 ∨ r ω = 1) ∧
    μ {ω | r ω = 1} = (1 / 2 : ℝ≥0∞) ∧ μ {ω | r ω = -1} = (1 / 2 : ℝ≥0∞)

/-- Evaluate a multilinear polynomial using real random inputs; the sample space need
not be finite. [OD14, Cor. 9.6] -/
noncomputable def evalMultilinearRV {n : ℕ}
    (F : ThresholdFunctions.MultilinearPolynomial n) (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ S : Finset (Fin n), F S * ∏ i ∈ S, X i ω

/-- A discrete law has atom masses at least `lam` when a finite set supports it almost
surely and every listed atom has that minimum mass. For positive `lam` this captures the
source's positive minimum probability, without restricting the sample space.
[OD14, Prop. 10.17] -/
def HasAtomLowerBound (X : Ω → ℝ) (μ : Measure Ω) (lam : ℝ) : Prop :=
  ∃ s : Finset ℝ, (∀ᵐ ω ∂μ, X ω ∈ s) ∧
    ∀ x ∈ s, ENNReal.ofReal lam ≤ μ {ω | X ω = x}

end BooleanAnalysis.Hypercontractivity
