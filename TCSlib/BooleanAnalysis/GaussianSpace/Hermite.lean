/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.HermiteDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Algebra.MvPolynomial.Degrees

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hermite expansions and Gaussian spectral theory: statement layer

## Main definitions

* `hermiteL2`: the L² class of the concrete normalized Hermite function.
  Its membership obligation is explicitly stated before the adapter.

## Main results

Finite Gaussian moments of Hermite functions follow from general polynomial moments.
Hermite orthonormality, completeness, expansions, Parseval/Plancherel, the noise
spectrum, and the strong generator spectrum/domain remain statements with placeholders.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Propositions 11.30–11.40 and Exercise 11.18.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- The normalized Hermites have the exponential generating function used to
define the source polynomials. [OD14, Def. 11.29, equation (11.8)]
**Proof sketch.** Expand `exp(tx-t²/2)` into a power series and compare its
coefficient recurrence with Mathlib's probabilists' Hermite recurrence. -/
theorem normalizedHermite_generating_function (x t : ℝ) :
    HasSum (fun j : ℕ => (normalizedHermitePolynomial j).eval x *
      t ^ j / Real.sqrt (j.factorial : ℝ)) (Real.exp (t * x - t ^ 2 / 2)) := sorry

/-- The product Hermite polynomial has total degree the sum of its indices.
[OD14, Def. 11.32] **Proof sketch.** Multiply the nonzero leading terms of the
scalar Hermites in their distinct coordinate variables. -/
theorem multivariateHermitePolynomial_totalDegree (α : Fin n → ℕ) :
    (multivariateHermitePolynomial α).totalDegree = ∑ i, α i := sorry

/-- An indicator multi-index gives the ordinary squarefree monomial.
[OD14, Def. 11.32; Remark 11.35]
**Proof sketch.** The scalar normalized Hermites of degree zero and one are
one and the coordinate, so their product is the indicated monomial. -/
theorem hermiteFunction_indicator (S : Finset (Fin n)) (x : Fin n → ℝ) :
    hermiteFunction (fun i => if i ∈ S then 1 else 0) x = ∏ i ∈ S, x i := sorry

/-- Every multivariate Hermite function has every finite Gaussian moment.
[OD14, §11.2] **Proof sketch.** Apply the existing moment theorem for multivariate
Gaussian polynomials to the concrete Hermite polynomial. -/
theorem hermiteFunction_memLp (α : Fin n → ℕ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (hermiteFunction α) p γ := by
  simpa only [hermiteFunction] using
    memLp_eval_gaussian (multivariateHermitePolynomial α) hp

/-- Every Hermite function belongs to Gaussian L². [OD14, Props. 11.30 and 11.33]
**Proof sketch.** Specialize finite Gaussian polynomial moments at exponent two. -/
theorem hermiteFunction_memLp_two (α : Fin n → ℕ) :
    MemLp (hermiteFunction α) 2 γ := sorry

/-- The Gaussian L² class represented by a normalized Hermite function.
[OD14, Props. 11.30 and 11.33] The concrete polynomial has already been defined;
the preceding membership obligation supplies only its passage to the quotient. -/
noncomputable def hermiteL2 (α : Fin n → ℕ) : Lp ℝ 2 γ :=
  (hermiteFunction_memLp_two α).toLp (hermiteFunction α)

/-- The multivariate Hermite functions form an orthonormal Gaussian L² family.
[OD14, Props. 11.30 and 11.33] **Proof sketch.** Factor Gaussian product integrals
into scalar orthogonality integrals, obtained by repeated integration by parts. -/
theorem hermiteL2_orthonormal (n : ℕ) :
    Orthonormal ℝ (@hermiteL2 n) := sorry

/-- The Hermite family spans a dense subspace of Gaussian L², including the
zero-dimensional case. [OD14, Props. 11.30 and 11.33]

**Proof sketch.** Triangular leading terms show that Hermites span all
polynomials, and Gaussian polynomial density gives completeness. -/
theorem hermiteL2_dense :
    Dense (↑(Submodule.span ℝ (Set.range (@hermiteL2 n))) : Set (Lp ℝ 2 γ)) := sorry

/-- The correlated moment of two Hermite functions vanishes off the diagonal;
on the diagonal it is correlation raised to total degree.
[OD14, Prop. 11.31 and its coordinate-product consequence]

**Proof sketch.** Use scalar generating functions for correlated Gaussians,
then factor across coordinates and compare coefficients. -/
theorem hermite_correlated_moment (α β : Fin n → ℕ) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (∫ z, hermiteFunction α z.1 * hermiteFunction β z.2
      ∂correlatedGaussianMeasure ρ) = if α = β then ρ ^ (∑ i, α i) else 0 := sorry

/-- Hermite functions are Gaussian noise eigenfunctions of their total degree.
[OD14, Prop. 11.37] **Proof sketch.** Apply the scalar conditional Hermite
identity coordinatewise and integrate the independent noise coordinates. -/
theorem gaussianNoise_hermiteFunction (α : Fin n → ℕ) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianNoise ρ (hermiteFunction α) =
      fun x => ρ ^ (∑ i, α i) * hermiteFunction α x := sorry

/-- A Gaussian L² function equals its Hermite expansion in the L² topology.
[OD14, Def. 11.34; Prop. 11.36] **Proof sketch.** Apply the complete orthonormal
family expansion theorem, identifying coefficients with Gaussian inner products. -/
theorem hermite_expansion (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    HasSum (fun α : Fin n → ℕ => hermiteCoeff f α • hermiteL2 α) (hf.toLp f) := sorry

/-- Coefficients of an L² Hermite expansion are unique.
[OD14, Def. 11.34] **Proof sketch.** Pair the convergent series with each
orthonormal basis vector; every other coefficient vanishes. -/
theorem hermite_expansion_unique (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ)
    (c : (Fin n → ℕ) → ℝ)
    (hc : HasSum (fun α => c α • hermiteL2 α) (hf.toLp f)) :
    c = hermiteCoeff f := sorry

/-- Hermite sums truncated by total degree converge to the function in L².
[OD14, Def. 11.34, displayed expansion]
**Proof sketch.** Restrict the complete orthonormal expansion to the increasing
finite sets of multi-indices of total degree at most the cutoff. -/
theorem hermite_degree_truncation_tendsto (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    Tendsto (fun k : ℕ => eLpNorm (fun x => f x -
      ∑ a : Fin n → Fin (k + 1), if (∑ i, (a i : ℕ)) ≤ k then
        hermiteCoeff f (fun i => (a i : ℕ)) * hermiteFunction (fun i => (a i : ℕ)) x else 0)
      2 γ) atTop (𝓝 0) := sorry

/-- The existing multilinear coefficients equal Hermite coefficients on
squarefree indices and vanish on all other indices. [OD14, Remark 11.35]

**Proof sketch.** Identify squarefree Hermites with monomials, expand the
existing multilinear evaluation, and apply Hermite orthogonality. -/
theorem hermiteCoeff_multilinear (F : MultilinearPolynomial n) (α : Fin n → ℕ) :
    hermiteCoeff (Hypercontractivity.evalMultilinearRV F (fun i z => z i)) α =
      if ∀ i, α i ≤ 1 then F (Finset.univ.filter fun i => α i = 1) else 0 := sorry

/-- The constant Hermite coefficient is the Gaussian mean.
[OD14, Prop. 11.36] **Proof sketch.** The degree-zero Hermite function is one. -/
theorem hermiteCoeff_zero (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    hermiteCoeff f (fun _ => 0) = ∫ x, f x ∂γ := sorry

/-- Gaussian variance is the squared Hermite spectrum away from the constant
index. [OD14, Prop. 11.36] **Proof sketch.** Apply Parseval to the centered
function and remove its zero constant coefficient. -/
theorem variance_eq_hermite (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    ProbabilityTheory.variance f γ =
      ∑' α : Fin n → ℕ, if α = 0 then 0 else (hermiteCoeff f α) ^ 2 := sorry

/-- The Gaussian inner product is the sum of products of Hermite coefficients.
[OD14, Prop. 11.36] **Proof sketch.** Pair the two L² expansions and use
orthonormality; Cauchy–Schwarz justifies the scalar series. -/
theorem hermite_plancherel (f g : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    (∫ x, f x * g x ∂γ) =
      ∑' α : Fin n → ℕ, hermiteCoeff f α * hermiteCoeff g α := sorry

/-- Gaussian noise multiplies each Hermite coefficient by correlation to degree.
[OD14, Prop. 11.37] **Proof sketch.** Move noise across the coefficient inner
product using self-adjointness, then use the Hermite eigenfunction identity. -/
theorem hermiteCoeff_gaussianNoise (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (α : Fin n → ℕ) :
    hermiteCoeff (gaussianNoise ρ f) α =
      ρ ^ (∑ i, α i) * hermiteCoeff f α := sorry

/-- Gaussian stability equals the degree-weighted squared Hermite spectrum.
[OD14, Prop. 11.37] **Proof sketch.** Apply Plancherel to a function and its
noisy version, then insert the coefficient multiplier identity. -/
theorem gaussianNoiseStability_hermite (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianNoiseStability ρ f =
      ∑' α : Fin n → ℕ, ρ ^ (∑ i, α i) * (hermiteCoeff f α) ^ 2 := sorry

/-- The positive Gaussian generator multiplies Hermite coefficients by degree.
[OD14, Prop. 11.40] **Proof sketch.** Pair its strong difference quotients with
a Hermite function and differentiate the scalar correlation eigenvalue. -/
theorem hermiteCoeff_gaussianGenerator (f g : (Fin n → ℝ) → ℝ)
    (hfg : HasGaussianGenerator f g) (α : Fin n → ℕ) :
    hermiteCoeff g α = ((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α := sorry

/-- The strong generator has the degree-weighted Hermite expansion in L².
[OD14, Prop. 11.40] **Proof sketch.** Expand the generator output in the Hermite
basis and replace its coefficients using the preceding multiplier formula. -/
theorem gaussianGenerator_hermite_expansion (f g : (Fin n → ℝ) → ℝ)
    (hfg : HasGaussianGenerator f g) :
    HasSum (fun α : Fin n → ℕ =>
      (((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α) • hermiteL2 α)
      (hfg.2.1.toLp g) := sorry

/-- A Gaussian L² function is in the generator domain exactly when its Hermite
coefficients weighted by degree are square summable.
[OD14, Prop. 11.40; Ex. 11.18]

**Proof sketch.** Necessity is Parseval for the generator. Conversely the
degree-weighted series defines an L² output, and dominated convergence proves
the required strong convergence of the noise difference quotients. -/
theorem gaussianGeneratorDomain_iff_hermite (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) :
    InGaussianGeneratorDomain f ↔ Summable (fun α : Fin n → ℕ =>
      (((∑ i, α i : ℕ) : ℝ) ^ 2) * (hermiteCoeff f α) ^ 2) := sorry

end BooleanAnalysis.GaussianSpace
