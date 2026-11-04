/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Orthogonality
import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Span
import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Gaussian Hermite Hilbert basis

## Main definitions

* `hermiteL2`: the Gaussian L² class of a Hermite polynomial.
* `hermiteHilbertBasis`: the complete orthonormal Hermite basis of Gaussian L².

## Main results

Finite Gaussian moments, orthonormality, completeness, uniqueness of expansions,
Plancherel, square summability of coefficients, and the variance identity.
Coefficient continuity and realization of square-summable spectra are also provided.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Propositions 11.30, 11.33, and 11.36.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

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
    MemLp (hermiteFunction α) 2 γ := by
  apply hermiteFunction_memLp
  norm_num

/-- The Gaussian L² class represented by a normalized Hermite function.
[OD14, Props. 11.30 and 11.33] The concrete polynomial has already been defined;
the preceding membership obligation supplies only its passage to the quotient. -/
noncomputable def hermiteL2 (α : Fin n → ℕ) : Lp ℝ 2 γ :=
  (hermiteFunction_memLp_two α).toLp (hermiteFunction α)

/-- Polynomial evaluation into Gaussian L² sends a multivariate Hermite polynomial
to its Hermite L² class. [OD14, Def. 11.32; Prop. 11.33] -/
lemma gaussianPolynomialLp_hermite (α : Fin n → ℕ) :
    gaussianPolynomialLp (n := n) ℝ 2 (by norm_num) (multivariateHermitePolynomial α) =
      hermiteL2 α := by
  rfl

/-- Every polynomial L² class is a finite linear combination of Hermite L² classes.
[OD14, Prop. 11.33]

**Proof sketch.** Map the algebraic spanning identity through the linear map
that evaluates polynomials and takes their Gaussian L² classes. -/
lemma gaussianPolynomialLp_mem_span_hermiteL2 (P : MvPolynomial (Fin n) ℝ) :
    gaussianPolynomialLp (n := n) ℝ 2 (by norm_num) P ∈
      Submodule.span ℝ (Set.range (@hermiteL2 n)) := by
  have hle :
      Submodule.span ℝ (Set.range (@multivariateHermitePolynomial n)) ≤
        (Submodule.span ℝ (Set.range (@hermiteL2 n))).comap
          (gaussianPolynomialLp (n := n) ℝ 2 (by norm_num)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    change gaussianPolynomialLp (n := n) ℝ 2 (by norm_num)
      (multivariateHermitePolynomial α) ∈ Submodule.span ℝ (Set.range (@hermiteL2 n))
    rw [gaussianPolynomialLp_hermite]
    exact Submodule.subset_span ⟨α, rfl⟩
  exact hle (by
    rw [span_multivariateHermitePolynomial_eq_top]
    trivial)

/-- The inner product of two Gaussian L² classes is the Gaussian integral of
the product of their chosen representatives.

**Proof sketch.** Replace both quotient representatives almost everywhere by
the original functions in the integral defining the L² inner product. -/
private lemma inner_toLp_eq_integral_mul (f g : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂γ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]
  simp [mul_comm]

/-- Inner products of the Gaussian L² Hermite classes are Kronecker deltas.
[OD14, Props. 11.30 and 11.33]

**Proof sketch.** Replace the L² classes by their almost-everywhere polynomial
representatives and apply the coordinate-product orthogonality identity. -/
lemma inner_hermiteL2 (α β : Fin n → ℕ) :
    inner ℝ (hermiteL2 α) (hermiteL2 β) = if α = β then 1 else 0 := by
  simpa only [hermiteL2, inner_toLp_eq_integral_mul] using
    integral_hermiteFunction_mul α β

/-- A Hermite function has coefficient one at its own index and zero elsewhere.
[OD14, Props. 11.30 and 11.33] -/
@[simp] lemma hermiteCoeff_hermiteFunction (α β : Fin n → ℕ) :
    hermiteCoeff (hermiteFunction α) β = if α = β then 1 else 0 := by
  simpa only [hermiteCoeff] using integral_hermiteFunction_mul α β

/-- The coefficient of a finite Hermite combination is the sum of its weights
at the requested index. Repeated indices contribute their combined weights.
[OD14, Def. 11.34; Prop. 11.36]

**Proof sketch.** Move the finite sum through the coefficient integral and use
orthogonality. Gaussian L² membership and Hölder ensure integrability of each product. -/
lemma hermiteCoeff_finset_sum_hermiteFunction {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (a : ι → (Fin n → ℕ)) (β : Fin n → ℕ) :
    hermiteCoeff (fun x => ∑ i ∈ s, c i * hermiteFunction (a i) x) β =
      ∑ i ∈ s, if a i = β then c i else 0 := by
  classical
  unfold hermiteCoeff
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finset_sum s
    (f := fun i x => c i * (hermiteFunction (a i) x * hermiteFunction β x))
    (fun i _ => by
      simpa only [Pi.mul_apply] using
        ((hermiteFunction_memLp_two (a i)).integrable_mul
          (hermiteFunction_memLp_two β)).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, integral_hermiteFunction_mul]
  by_cases h : a i = β <;> simp [h]

/-- The multivariate Hermite functions form an orthonormal Gaussian L² family.
[OD14, Props. 11.30 and 11.33] **Proof sketch.** Factor Gaussian product integrals
into scalar orthogonality integrals, obtained by repeated integration by parts. -/
theorem hermiteL2_orthonormal (n : ℕ) :
    Orthonormal ℝ (@hermiteL2 n) := by
  classical
  exact orthonormal_iff_ite.mpr inner_hermiteL2

/-- The Hermite family spans a dense subspace of Gaussian L², including the
zero-dimensional case. [OD14, Props. 11.30 and 11.33]

**Proof sketch.** Triangular leading terms show that Hermites span all
polynomials, and Gaussian polynomial density gives completeness. -/
theorem hermiteL2_dense :
    Dense (↑(Submodule.span ℝ (Set.range (@hermiteL2 n))) : Set (Lp ℝ 2 γ)) := by
  intro f
  rw [EMetric.mem_closure_iff]
  intro ε hε
  obtain ⟨P, hP⟩ := gaussian_polynomial_dense 2 (by norm_num) (by norm_num)
    (Lp.memLp f) ε hε
  refine ⟨gaussianPolynomialLp (n := n) ℝ 2 (by norm_num) P,
    gaussianPolynomialLp_mem_span_hermiteL2 P, ?_⟩
  change edist f ((memLp_eval_gaussian P (p := 2) (by norm_num)).toLp
    (fun x : Fin n → ℝ => MvPolynomial.eval x P)) < ε
  rw [← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]
  exact hP

/-- The normalized multivariate Hermite classes form a Gaussian L² Hilbert basis.
[OD14, Props. 11.30 and 11.33] -/
noncomputable def hermiteHilbertBasis : HilbertBasis (Fin n → ℕ) ℝ (Lp ℝ 2 γ) :=
  HilbertBasis.mk (hermiteL2_orthonormal n)
    (Submodule.dense_iff_topologicalClosure_eq_top.mp hermiteL2_dense).ge

/-- The Hermite Hilbert basis vector at each multi-index is its concrete Hermite
L² class. [OD14, Def. 11.32; Prop. 11.33] -/
@[simp] lemma hermiteHilbertBasis_apply (α : Fin n → ℕ) :
    hermiteHilbertBasis α = hermiteL2 α := by
  simp [hermiteHilbertBasis]

/-- Pairing an L² function with a Hermite vector gives its Hermite coefficient.
[OD14, Def. 11.34]

**Proof sketch.** Replace both L² classes by their almost-everywhere
representatives in the integral defining the inner product. -/
lemma inner_hermiteL2_toLp (α : Fin n → ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) :
    inner ℝ (hermiteL2 α) (hf.toLp f) = hermiteCoeff f α := by
  simpa only [hermiteL2, hermiteCoeff, mul_comm] using
    inner_toLp_eq_integral_mul (hermiteFunction α) f (hermiteFunction_memLp_two α) hf

/-- Pairing a Gaussian L² function with a Hermite vector gives its Hermite
coefficient. [OD14, Def. 11.34] -/
lemma inner_toLp_hermiteL2 (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ)
    (α : Fin n → ℕ) :
    inner ℝ (hf.toLp f) (hermiteL2 α) = hermiteCoeff f α := by
  rw [real_inner_comm]
  exact inner_hermiteL2_toLp α f hf

/-- Coordinates in the Gaussian Hermite Hilbert basis equal the concrete Hermite
coefficients. [OD14, Def. 11.34] -/
lemma hermiteHilbertBasis_repr_toLp (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ)
    (α : Fin n → ℕ) :
    hermiteHilbertBasis.repr (hf.toLp f) α = hermiteCoeff f α := by
  rw [HilbertBasis.repr_apply_apply, hermiteHilbertBasis_apply,
    inner_hermiteL2_toLp]

/-- A Gaussian L² function equals its Hermite expansion in the L² topology.
[OD14, Def. 11.34; Prop. 11.36] **Proof sketch.** Apply the complete orthonormal
family expansion theorem, identifying coefficients with Gaussian inner products. -/
theorem hermite_expansion (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    HasSum (fun α : Fin n → ℕ => hermiteCoeff f α • hermiteL2 α) (hf.toLp f) := by
  simpa only [hermiteHilbertBasis_repr_toLp, hermiteHilbertBasis_apply] using
    hermiteHilbertBasis.hasSum_repr (hf.toLp f)

/-- Coefficients of an L² Hermite expansion are unique.
[OD14, Def. 11.34] **Proof sketch.** Pair the convergent series with each
orthonormal basis vector; every other coefficient vanishes. -/
theorem hermite_expansion_unique (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ)
    (c : (Fin n → ℕ) → ℝ)
    (hc : HasSum (fun α => c α • hermiteL2 α) (hf.toLp f)) :
    c = hermiteCoeff f := by
  classical
  funext α
  have h := hc.mapL (innerSL ℝ (hermiteL2 α))
  simp only [innerSL_apply, inner_smul_right, inner_hermiteL2,
    inner_hermiteL2_toLp] at h
  apply (hasSum_ite_eq α (c α)).unique
  convert h using 1
  funext β
  by_cases hβα : β = α
  · subst β
    simp
  · simp [hβα, Ne.symm hβα]

set_option linter.unusedVariables false in
/-- The constant Hermite coefficient is the Gaussian mean.
[OD14, Prop. 11.36] The L² hypothesis is retained for consistency with the coefficient
API, although this identity holds without it.
**Proof sketch.** The degree-zero Hermite function is one. -/
theorem hermiteCoeff_zero (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    hermiteCoeff f (fun _ => 0) = ∫ x, f x ∂γ := by
  simp [hermiteCoeff]

/-- The squares of a Gaussian L² function's Hermite coefficients form a summable
family. [OD14, Prop. 11.36]

**Proof sketch.** Apply Hilbert-basis summability to the function paired with itself
and identify its coordinates with its Hermite coefficients. -/
lemma hermiteCoeff_sq_summable (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    Summable (fun α : Fin n → ℕ => (hermiteCoeff f α) ^ 2) := by
  simpa only [hermiteHilbertBasis_apply, inner_toLp_hermiteL2,
    inner_hermiteL2_toLp, pow_two] using
    hermiteHilbertBasis.summable_inner_mul_inner (hf.toLp f) (hf.toLp f)

/-- The Gaussian inner product is the sum of products of Hermite coefficients.
[OD14, Prop. 11.36] **Proof sketch.** Pair the two L² expansions and use
orthonormality; Cauchy–Schwarz justifies the scalar series. -/
theorem hermite_plancherel (f g : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    (∫ x, f x * g x ∂γ) =
      ∑' α : Fin n → ℕ, hermiteCoeff f α * hermiteCoeff g α := by
  simpa only [hermiteHilbertBasis_apply, inner_toLp_hermiteL2,
    inner_hermiteL2_toLp, inner_toLp_eq_integral_mul] using
    (hermiteHilbertBasis.tsum_inner_mul_inner (hf.toLp f) (hg.toLp g)).symm

/-- Gaussian variance is the squared Hermite spectrum away from the constant
index. [OD14, Prop. 11.36]

**Proof sketch.** Parseval expresses the second moment as the sum of all squared
Hermite coefficients. The zero coefficient is the Gaussian mean. Subtract its
square and remove that term from the summable spectrum. -/
theorem variance_eq_hermite (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    ProbabilityTheory.variance f γ =
      ∑' α : Fin n → ℕ, if α = 0 then 0 else (hermiteCoeff f α) ^ 2 := by
  letI : IsProbabilityMeasure standardGaussianMeasure :=
    inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))
  have hparse : (∫ x, f x ^ 2 ∂γ) = ∑' α, (hermiteCoeff f α) ^ 2 := by
    simpa only [pow_two] using hermite_plancherel f f hf hf
  rw [ProbabilityTheory.variance_eq_sub hf]
  simp only [Pi.pow_apply]
  rw [hparse,
    (hermiteCoeff_sq_summable f hf).tsum_eq_add_tsum_ite 0]
  simp only [Pi.zero_def, hermiteCoeff_zero f hf]
  ring

/-- Multiplication by a real constant scales every Hermite coefficient.
[OD14, Def. 11.34] -/
lemma hermiteCoeff_const_mul (c : ℝ) (f : (Fin n → ℝ) → ℝ) (α : Fin n → ℕ) :
    hermiteCoeff (fun x => c * f x) α = c * hermiteCoeff f α := by
  simp only [hermiteCoeff, mul_assoc, integral_const_mul]

/-- Hermite coefficients preserve subtraction of Gaussian L² functions.
[OD14, Def. 11.34] -/
lemma hermiteCoeff_sub (f g : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) (α : Fin n → ℕ) :
    hermiteCoeff (fun x => f x - g x) α = hermiteCoeff f α - hermiteCoeff g α := by
  simp only [hermiteCoeff, sub_mul]
  exact integral_sub
    (f := fun x => f x * hermiteFunction α x)
    (g := fun x => g x * hermiteFunction α x)
    (hf.integrable_mul (hermiteFunction_memLp_two α))
    (hg.integrable_mul (hermiteFunction_memLp_two α))

/-- Each Hermite coefficient is bounded in absolute value by the Gaussian L² norm.
[OD14, Props. 11.30, 11.33, and 11.36]

**Proof sketch.** Express the coefficient as an L² inner product and apply
Cauchy–Schwarz. The Hermite vector has norm one. -/
lemma abs_hermiteCoeff_le_eLpNorm_toReal (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (α : Fin n → ℕ) :
    |hermiteCoeff f α| ≤ (eLpNorm f 2 γ).toReal := by
  simpa only [inner_hermiteL2_toLp α f hf,
    (hermiteL2_orthonormal n).norm_eq_one α, one_mul, Lp.norm_toLp] using
    abs_real_inner_le_norm (hermiteL2 α) (hf.toLp f)

/-- Gaussian L² convergence implies convergence of each Hermite coefficient.
The approximating functions need belong to L² only eventually.
[OD14, Def. 11.34; Prop. 11.36]

**Proof sketch.** Bound the coefficient difference by the L² norm of the
function difference, which tends to zero. -/
lemma tendsto_hermiteCoeff_of_eLpNorm_sub_tendsto {ι : Type*} {l : Filter ι}
    (u : ι → (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ)
    (hu : ∀ᶠ i in l, MemLp (u i) 2 γ)
    (hlim : Tendsto (fun i => eLpNorm (fun x => u i x - f x) 2 γ) l (𝓝 0))
    (α : Fin n → ℕ) :
    Tendsto (fun i => hermiteCoeff (u i) α) l (𝓝 (hermiteCoeff f α)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero'
    (g := fun i => (eLpNorm (fun x => u i x - f x) 2 γ).toReal)
    (Eventually.of_forall fun i => norm_nonneg _) ?_ ?_
  · filter_upwards [hu] with i hi
    simpa only [Real.norm_eq_abs, hermiteCoeff_sub (u i) f hi hf α] using
      abs_hermiteCoeff_le_eLpNorm_toReal
        (fun x => u i x - f x) (hi.sub hf) α
  · simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlim

/-- Every square-summable real family is the Hermite coefficient family of a
Gaussian L² function. [OD14, Props. 11.33 and 11.36]

**Proof sketch.** Regard the coefficients as an element of sequence ℓ² and apply
the inverse Hermite basis representation. Choose the resulting L² representative. -/
lemma exists_memLp_hermiteCoeff (c : (Fin n → ℕ) → ℝ)
    (hc : Summable (fun α => (c α) ^ 2)) :
    ∃ g : (Fin n → ℝ) → ℝ, MemLp g 2 γ ∧ hermiteCoeff g = c := by
  have hc' : Memℓp c 2 := by
    apply (memℓp_gen_iff (p := 2) (by norm_num)).2
    simpa [Real.rpow_two, Real.norm_eq_abs] using hc
  let q : lp (fun _ : Fin n → ℕ => ℝ) 2 := ⟨c, hc'⟩
  let v : Lp ℝ 2 γ := hermiteHilbertBasis.repr.symm q
  refine ⟨v, Lp.memLp v, ?_⟩
  funext α
  rw [← hermiteHilbertBasis_repr_toLp v (Lp.memLp v) α, Lp.toLp_coeFn]
  simp [v, q]

/-- The Gaussian L² norm is the square root of the sum of squared Hermite
coefficients. [OD14, Prop. 11.36]

**Proof sketch.** Parseval identifies the squared L² norm with the squared
coefficient sum. Take its nonnegative square root and recover the extended norm. -/
lemma eLpNorm_two_eq_sqrt_hermiteCoeff (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 γ) :
    eLpNorm f 2 γ =
      ENNReal.ofReal (Real.sqrt (∑' α : Fin n → ℕ, (hermiteCoeff f α) ^ 2)) := by
  have hsq : ‖hf.toLp f‖ ^ 2 = ∑' α : Fin n → ℕ, (hermiteCoeff f α) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_integral_mul f f hf hf,
      hermite_plancherel f f hf hf]
    simp only [pow_two]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _), Lp.norm_toLp,
    ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

end BooleanAnalysis.GaussianSpace
