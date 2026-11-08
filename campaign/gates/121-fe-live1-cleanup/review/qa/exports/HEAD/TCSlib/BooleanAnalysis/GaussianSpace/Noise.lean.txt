/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Linear
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Kernel
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Density
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Fourier
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Continuity
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Polynomial
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Exponential
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Torus
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.PolynomialApproximation
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.BlockCharacteristic
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.BooleanCharacteristic
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.UniformTransfer
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.BooleanBounds
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.ContinuousBounds
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.TorusApproximation
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.FatouBound
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.LpBounds
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.MeanBound
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Exponents
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.HypercontractivePairing
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Duality
import TCSlib.BooleanAnalysis.GaussianSpace.IndicatorSmoothing
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance
import Mathlib.Algebra.MvPolynomial.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian noise and hypercontractivity

## Contents

* `Noise.Linear`: linear symmetries of finite Gaussian product laws.
* `Noise.Kernel`: Gaussian kernel integration and composition.
* `Noise.Density`: pointwise integrability of Gaussian kernels.
* `Noise.Fourier`: smooth Gaussian Fourier averages.
* `Noise.Continuity`: continuity of Gaussian averaging at correlation one.
* `Noise.Polynomial`: expectations of affine Gaussian monomials.
* `Noise.Exponential`: Gaussian exponential envelopes and Taylor convergence.
* `Noise.Torus`: compact Fourier approximation through a measurable embedding.
* `Noise.PolynomialApproximation`: density of polynomial evaluation classes.
* `Noise.BlockCharacteristic`: correlated Boolean block characteristic limits.
* `Noise.BooleanCharacteristic`: finite noise-kernel Fourier expectations.
* `Noise.UniformTransfer`: compact continuous transfer from Boolean blocks.
* `Noise.BooleanBounds`: Boolean pairing bounds with positive exponent offsets.
* `Noise.ContinuousBounds`: Gaussian pairing estimates for compact approximants.
* `Noise.TorusApproximation`: Lp and almost-everywhere compact approximation.
* `Noise.FatouBound`: integrability from nonnegative limiting bounds.
* `Noise.LpBounds`: Gaussian pairing estimates in the prescribed Lp spaces.
* `Noise.MeanBound`: the probability-space mean bound at all Lp exponents.
* `Noise.Exponents`: finite-exponent and endpoint threshold arithmetic.
* `Noise.HypercontractivePairing`: bounded dual tests for Gaussian averaging.
* `Noise.Duality`: recover Lq membership and norm bounds from bounded Hölder tests.

## Main definitions

The concrete definitions are in `NoiseDefinitions`. Lp spaces, product Gaussian
laws, multilinear evaluation and averaged indicators reuse the existing APIs.

## Main results

Correlated-law symmetry, the Mehler semigroup, Lp contraction, smoothing,
continuity at correlation one, polynomial density and both Gaussian
hypercontractive inequalities.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Fact 11.7, Fact 11.13,
  Propositions 11.15–11.17, Theorems 11.22–11.23 and Gaussian Hypercontractivity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- The first marginal of a correlated standard Gaussian pair is standard Gaussian.
[OD14, Def. 11.10] **Proof sketch.** Cancel the first projection of the defining
pushforward and use the product marginal formula. -/
theorem correlatedGaussianMeasure_fst (ρ : ℝ) :
    (correlatedGaussianMeasure (n := n) ρ).map Prod.fst = γ := by
  unfold correlatedGaussianMeasure
  rw [Measure.map_map measurable_fst (by fun_prop)]
  exact measurePreserving_fst.map_eq

/-- The second marginal is standard Gaussian for every valid correlation.
[OD14, Fact 11.7] **Proof sketch.** The independent Gaussian linear combination
has mean zero and covariance the identity; transport its product law. -/
theorem correlatedGaussianMeasure_snd {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure (n := n) ρ).map Prod.snd = γ := by
  unfold correlatedGaussianMeasure
  rw [Measure.map_map measurable_snd (by fun_prop)]
  exact (measurePreserving_gaussianEndpoint hρ).map_eq

/-- Interchanging the endpoints preserves the correlated Gaussian law.
[OD14, Remark 11.11] **Proof sketch.** Apply Gaussian rotation invariance to
the independent pair and compare the resulting endpoints. -/
theorem correlatedGaussianMeasure_swap {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure (n := n) ρ).map Prod.swap =
      correlatedGaussianMeasure ρ := by
  let C := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    (z.1, fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i)
  let R := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    (fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i,
     fun i => Real.sqrt (1 - ρ ^ 2) * z.1 i - ρ * z.2 i)
  have hR : MeasurePreserving R ((γ).prod γ) ((γ).prod γ) := by
    simpa only [Real.cos_arccos hρ.1 hρ.2, Real.sin_arccos] using
      (measurePreserving_gaussianReflection (n := n) (Real.arccos ρ))
  have hC : C ∘ R = Prod.swap ∘ C := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - ρ ^ 2 by nlinarith [hρ.1, hρ.2])
    ext z i
    · rfl
    · dsimp [C, R]
      nlinarith [congrArg (fun t : ℝ => t * z.1 i) hs]
  change (((γ).prod γ).map C).map Prod.swap = ((γ).prod γ).map C
  rw [Measure.map_map measurable_swap (by dsimp [C]; fun_prop), ← hC,
    ← Measure.map_map (by dsimp [C]; fun_prop) hR.measurable, hR.map_eq]

/-- Two unit-vector Gaussian projections have the correlated scalar law with
correlation their inner product. [OD14, Fact 11.7]
**Proof sketch.** Compare characteristic functions of the two joint laws.
Independence expresses their exponents as quadratic forms. The unit-vector
assumptions and the inner product identity make these forms equal. -/
theorem gaussian_projection_pair_law {d : ℕ} (a b : Fin d → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (ρ : ℝ) (hab : ∑ i, a i * b i = ρ) :
    (Measure.pi fun _ : Fin d => standardGaussianMeasure).map
        (fun z => (∑ i, a i * z i, ∑ i, b i * z i)) =
      (standardGaussianMeasure.prod standardGaussianMeasure).map
        (fun z => (z.1, ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)) := by
  let A : (Fin d → ℝ) →L[ℝ] ℝ := ∑ i, a i • ContinuousLinearMap.proj i
  let B : (Fin d → ℝ) →L[ℝ] ℝ := ∑ i, b i • ContinuousLinearMap.proj i
  let C : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ρ • ContinuousLinearMap.fst ℝ ℝ ℝ +
        Real.sqrt (1 - ρ ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  suffices h : (Measure.pi fun _ : Fin d => standardGaussianMeasure).map (A.prod B) =
      (standardGaussianMeasure.prod standardGaussianMeasure).map C by
    convert h using 2
    funext z
    simp [A, B, ContinuousLinearMap.sum_apply]
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_gaussianPi, charFunDual_map,
    charFunDual_prod, charFunDual_standardGaussian, charFunDual_standardGaussian,
    ← Complex.exp_add]
  simp [A, B, C, ContinuousLinearMap.sum_apply, Pi.single_apply, mul_ite]
  have hρsq : ρ ^ 2 ≤ 1 := by
    simpa [ha, hb, hab] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hs := Real.sq_sqrt (show 0 ≤ 1 - ρ ^ 2 by linarith)
  have hvar : ∑ i, L (a i, b i) ^ 2 =
      L (1, ρ) ^ 2 + L (0, Real.sqrt (1 - ρ ^ 2)) ^ 2 := by
    calc
      _ = ∑ i, (L (1, 0) * a i + L (0, 1) * b i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [realLinearFunctional_pair]
        ring
      _ = _ := by
        rw [sum_sq_projectionCoefficients, ha, hb, hab,
          realLinearFunctional_pair L 1 ρ,
          realLinearFunctional_pair L 0 (Real.sqrt (1 - ρ ^ 2))]
        nlinarith [congrArg (fun t : ℝ => t * L (0, 1) ^ 2) hs]
  apply congrArg Complex.exp
  rw [← add_div, ← neg_add]
  congr 2
  exact_mod_cast hvar

/-- Applying the same orthogonal transformation to both endpoints preserves
the correlated Gaussian law. [OD14, Remark 11.11]
**Proof sketch.** Orthogonal invariance preserves each independent Gaussian
vector in the defining coupling, and linearity commutes with the endpoint map. -/
theorem correlatedGaussianMeasure_isometry (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (correlatedGaussianMeasure (n := n) ρ).map
      (fun z => (WithLp.ofLp (Q (WithLp.toLp 2 z.1)),
        WithLp.ofLp (Q (WithLp.toLp 2 z.2)))) = correlatedGaussianMeasure ρ := by
  rcases hρ with ⟨_, _⟩
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let q := e.symm.trans (Q.toContinuousLinearEquiv.trans e)
  let C := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    (z.1, fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i)
  let P := Prod.map q q
  have hP : MeasurePreserving P ((γ).prod γ) ((γ).prod γ) :=
    (measurePreserving_gaussianIsometry Q).prod (measurePreserving_gaussianIsometry Q)
  have hcomm : C ∘ P = P ∘ C := by
    funext z
    apply Prod.ext
    · rfl
    · change ρ • q z.1 + Real.sqrt (1 - ρ ^ 2) • q z.2 =
        q (ρ • z.1 + Real.sqrt (1 - ρ ^ 2) • z.2)
      rw [map_add, map_smul, map_smul]
  change (((γ).prod γ).map C).map P = ((γ).prod γ).map C
  rw [Measure.map_map hP.measurable (by dsimp [C]; fun_prop), ← hcomm,
    ← Measure.map_map (by dsimp [C]; fun_prop) hP.measurable, hP.map_eq]

/-- Gaussian averaging respects almost-everywhere equality on the Gaussian law.
[OD14, Def. 11.12] **Proof sketch.** Use the second marginal to transfer the null
exceptional set, then apply Fubini to its sections. -/
theorem gaussianNoise_congr_ae {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : (Fin n → ℝ) → ℝ} (hfg : f =ᵐ[γ] g) :
    gaussianNoise ρ f =ᵐ[γ] gaussianNoise ρ g := by
  filter_upwards [Measure.ae_ae_of_ae_prod
    ((measurePreserving_gaussianEndpoint hρ).quasiMeasurePreserving.ae hfg)] with x hx
  exact integral_congr_ae hx

/-- Correlation one leaves a function unchanged. [OD14, Def. 11.12]
**Proof sketch.** The Gaussian coefficient vanishes and the integral is constant. -/
theorem gaussianNoise_one (f : (Fin n → ℝ) → ℝ) : gaussianNoise 1 f = f := by
  funext x
  simp [gaussianNoise]

/-- Correlation zero replaces a function by its Gaussian mean. [OD14, Def. 11.12]
**Proof sketch.** The first endpoint disappears from the defining average. -/
theorem gaussianNoise_zero (f : (Fin n → ℝ) → ℝ) :
    gaussianNoise 0 f = fun _ => ∫ x, f x ∂γ := by
  funext x
  simp [gaussianNoise]

/-- Gaussian noise preserves the mean of an integrable function.
[OD14, §11.1] **Proof sketch.** Fubini and the second marginal identify the
iterated integral with the original Gaussian expectation. -/
theorem integral_gaussianNoise {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    (∫ x, gaussianNoise ρ f x ∂γ) = ∫ x, f x ∂γ := by
  let E := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i
  have hp : MeasurePreserving E ((γ).prod γ) γ := measurePreserving_gaussianEndpoint hρ
  calc
    _ = ∫ z, f (E z) ∂(γ).prod γ :=
      (integral_prod _ (hp.integrable_comp_of_integrable hf)).symm
    _ = _ := by
      conv_rhs => rw [← hp.map_eq]
      exact (integral_map hp.measurable.aemeasurable
        (hp.map_eq.symm ▸ hf.aestronglyMeasurable)).symm

/-- Composing Gaussian noise multiplies its correlation parameters.
[OD14, §11.1] **Proof sketch.** Combine the two independent Gaussian increments;
their variance is `1-(ρσ)²`. Fubini is justified by the Gaussian marginal law. -/
theorem gaussianNoise_compose {ρ σ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hσ : σ ∈ Set.Icc (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    gaussianNoise ρ (gaussianNoise σ f) =ᵐ[γ] gaussianNoise (ρ * σ) f := by
  have hfg := hf.aestronglyMeasurable.ae_eq_mk
  exact (gaussianNoise_congr_ae hρ (gaussianNoise_congr_ae hσ hfg)).trans
    ((gaussianNoise_compose_stronglyMeasurable hρ hσ (hf.congr hfg)
      hf.aestronglyMeasurable.stronglyMeasurable_mk).trans
        (gaussianNoise_congr_ae (correlation_mul_mem hρ hσ) hfg).symm)

/-- The product of two Gaussian square-integrable functions is integrable under
the correlated joint law. [OD14, §11.1, Gaussian noise inner product]

**Proof sketch.** Pull both square-integrability bounds through the marginal
projections and apply Cauchy–Schwarz. -/
lemma integrable_correlatedGaussianMeasure_mul {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    Integrable (fun z => f z.1 * g z.2) (correlatedGaussianMeasure ρ) := by
  exact (hf.comp_measurePreserving
    ⟨measurable_fst, correlatedGaussianMeasure_fst ρ⟩).integrable_mul
      (hg.comp_measurePreserving ⟨measurable_snd, correlatedGaussianMeasure_snd hρ⟩)

/-- The correlated joint integral equals its conditional-noise inner product.
[OD14, §11.1, Gaussian Hypercontractivity display]
**Proof sketch.** Expand the pushforward law and apply Fubini; the marginal
L² assumptions give joint integrability by Cauchy–Schwarz. -/
theorem integral_correlatedGaussianMeasure {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {f g : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    (∫ z, f z.1 * g z.2 ∂correlatedGaussianMeasure ρ) =
      ∫ x, f x * gaussianNoise ρ g x ∂γ := by
  exact integral_correlatedGaussianMeasure_of_integrable ρ
    (integrable_correlatedGaussianMeasure_mul hρ hf hg)

/-- Gaussian noise is self-adjoint on Gaussian L². [OD14, §11.1]
**Proof sketch.** Write the two sides as the integral over the correlated pair,
then use endpoint exchange; Cauchy–Schwarz supplies integrability. -/
theorem gaussianNoise_selfAdjoint {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    (∫ x, f x * gaussianNoise ρ g x ∂γ) = ∫ x, gaussianNoise ρ f x * g x ∂γ := by
  calc
    _ = ∫ z, f z.1 * g z.2 ∂correlatedGaussianMeasure ρ :=
      (integral_correlatedGaussianMeasure hρ hf hg).symm
    _ = ∫ z, g z.1 * f z.2 ∂correlatedGaussianMeasure ρ := by
      simpa only [MeasurableEquiv.prodComm, Equiv.prodComm, Equiv.coe_fn_mk,
        MeasurableEquiv.coe_mk, correlatedGaussianMeasure_swap hρ, mul_comm] using
        (integral_map_equiv (μ := correlatedGaussianMeasure ρ)
          (MeasurableEquiv.prodComm :
            ((Fin n → ℝ) × (Fin n → ℝ)) ≃ᵐ ((Fin n → ℝ) × (Fin n → ℝ)))
          (fun z => f z.1 * g z.2))
    _ = ∫ x, g x * gaussianNoise ρ f x ∂γ :=
      integral_correlatedGaussianMeasure hρ hg hf
    _ = _ := by simp only [mul_comm]

/-- Gaussian noise is additive on integrable functions.
[OD14, Def. 11.12] **Proof sketch.** Split the defining integral; interior
Gaussian kernels preserve integrability and endpoint kernels are deterministic. -/
theorem gaussianNoise_add {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f g : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) (hg : Integrable g γ) :
    gaussianNoise ρ (fun x => f x + g x) =
      fun x => gaussianNoise ρ f x + gaussianNoise ρ g x := by
  funext x
  exact integral_add (integrable_gaussianNoise_integrand hρ hf x)
    (integrable_gaussianNoise_integrand hρ hg x)

/-- Scalar multiplication commutes with Gaussian noise.
[OD14, Def. 11.12] **Proof sketch.** Move the scalar through the Bochner integral. -/
theorem gaussianNoise_const_mul (ρ c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    gaussianNoise ρ (fun x => c * f x) = fun x => c * gaussianNoise ρ f x := by
  funext x
  exact integral_const_mul c _

/-- Gaussian noise contracts the Lp norm, including both endpoint exponents.
[OD14, Prop. 11.15] **Proof sketch.** Integrate the conditional Jensen inequality,
or use the essential supremum bound when the exponent is infinite. -/
theorem gaussianNoise_contract {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (p : ℝ≥0∞) (hp : 1 ≤ p) {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p γ) :
    eLpNorm (gaussianNoise ρ f) p γ ≤ eLpNorm f p γ := by
  calc
    _ ≤ eLpNorm (f ∘ (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i)) p ((γ).prod γ) :=
      eLpNorm_integral_prod_le p hp
        (hf.comp_measurePreserving (measurePreserving_gaussianEndpoint hρ)).aestronglyMeasurable
    _ = _ := eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
      (measurePreserving_gaussianEndpoint hρ)

/-- Gaussian noise preserves every Lp space for `1 ≤ p ≤ ∞`.
[OD14, Prop. 11.15] **Proof sketch.** Jensen and the marginal identity bound the
norm at finite exponent; essential boundedness handles infinity. -/
theorem gaussianNoise_memLp {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (p : ℝ≥0∞) (hp : 1 ≤ p) {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p γ) :
    MemLp (gaussianNoise ρ f) p γ := by
  exact ⟨(hf.comp_measurePreserving
    (measurePreserving_gaussianEndpoint hρ)).aestronglyMeasurable.integral_prod_right',
      (gaussianNoise_contract hρ p hp hf).trans_lt hf.eLpNorm_lt_top⟩

/-- At interior correlations, Gaussian averaging makes any Gaussian L¹ function
smooth. [OD14, Prop. 11.16]

**Proof sketch.** Complete the square in the kernel density relative to the
standard Gaussian law. The remaining exponential kernel is a double Fourier
average: its inner average is uniformly bounded, and its outer Gaussian average
is smooth because every Gaussian norm moment is finite. Multiply by the smooth
starting-point factor. -/
theorem gaussianNoise_smooth {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (gaussianNoise ρ f) := by
  let s := Real.sqrt (1 - ρ ^ 2)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by nlinarith [hρ.1, hρ.2])
  have hvar : s ^ 2 + ρ ^ 2 = 1 := by
    dsimp [s]
    rw [Real.sq_sqrt (show 0 ≤ 1 - ρ ^ 2 by nlinarith [hρ.1, hρ.2])]
    ring
  have hfactor : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Fin n → ℝ =>
      (Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi * s ^ 2)) ^ n *
        Real.exp ((∑ i, x i ^ 2) / 2)) := by fun_prop
  convert hfactor.mul (contDiff_integral_gaussian_exp (1 / s) (-ρ / s) hf) using 1
  funext x
  exact integral_gaussianNoise_densityFactorization ρ s (ne_of_gt hspos) hvar f x

/-- Gaussian noise converges to the identity in L¹ as correlation tends to one.
[OD14, Prop. 11.17]

**Proof sketch.** Continuous Gaussian rotations induce continuous L1 pullbacks.
As the angle tends to zero, their joint endpoint error tends to zero. Averaging
the second coordinate bounds the noise error by this joint L1 error. -/
theorem gaussianNoise_tendsto_one {f : (Fin n → ℝ) → ℝ} (hf : Integrable f γ) :
    Tendsto (fun ρ : ℝ => eLpNorm (fun x => gaussianNoise ρ f x - f x) 1 γ)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hleft : ∀ᶠ ρ : ℝ in 𝓝[<] (1 : ℝ), -1 < ρ :=
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ ρ : ℝ in 𝓝[<] (1 : ℝ),
      eLpNorm (fun x => gaussianNoise ρ f x - f x) 1 γ ≤
        eLpNorm (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (fun i => Real.cos (Real.arccos ρ) * z.1 i +
            Real.sin (Real.arccos ρ) * z.2 i) - f z.1) 1 ((γ).prod γ) := by
    filter_upwards [hleft, self_mem_nhdsWithin] with ρ hl hr
    have hv : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨hl.le, hr.le⟩
    simpa only [Real.cos_arccos hv.1 hv.2, Real.sin_arccos] using
      eLpNorm_gaussianNoise_sub_le hv hf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_eLpNorm_gaussianEndpoint hf).mono_left nhdsWithin_le_nhds)
    (Eventually.of_forall fun _ => zero_le _) hbound

/-- On multilinear polynomials, Gaussian noise scales every input by correlation.
[OD14, Fact 11.13] **Proof sketch.** Expand into monomials and integrate the
independent centered noise coordinates; only the noise-free term survives. -/
theorem gaussianNoise_multilinear (F : MultilinearPolynomial n)
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x : Fin n → ℝ) :
    gaussianNoise ρ (evalMultilinearRV F (fun i z => z i)) x =
      evalMultilinearRV F (fun i z => z i) (fun i => ρ * x i) := by
  rcases hρ with ⟨_, _⟩
  classical
  unfold gaussianNoise evalMultilinearRV
  rw [integral_finset_sum _ (fun S _ =>
    (integrable_gaussian_affine_monomial (fun i => ρ * x i)
      (Real.sqrt (1 - ρ ^ 2)) S).const_mul (F S))]
  simp_rw [integral_const_mul, integral_gaussian_affine_monomial]

/-- General Gaussian noise agrees with the existing averaged-indicator operation.
[OD14, Def. 11.12; §11.4] **Proof sketch.** For angles in `[0,π]`, the nonnegative
sine equals the square root in the Mehler kernel, so the definitions agree. -/
theorem gaussianNoise_indicator_eq_averaged {A : Set (Fin n → ℝ)}
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    gaussianNoise (Real.cos θ) (A.indicator (fun _ => (1 : ℝ))) =
      averagedGaussianIndicator A θ := by
  unfold gaussianNoise averagedGaussianIndicator
  rw [← Real.sin_eq_sqrt_one_sub_cos_sq hθ.1 hθ.2]

/-- Multivariate polynomials are dense in Gaussian Lp for every finite `p ≥ 1`.
[OD14, Thm. 11.22]

**Proof sketch.** Embed the real coordinates measurably into a compact torus at
two incommensurable frequencies. Pull back dense Fourier monomials and approximate
their linear exponential phases by Taylor polynomials in Gaussian Lp. Taking real
parts of the complex polynomial coefficients gives the required real approximation. -/
theorem gaussian_polynomial_dense (p : ℝ≥0∞) (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p γ) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ P : MvPolynomial (Fin n) ℝ,
      eLpNorm (fun x => f x - MvPolynomial.eval x P) p γ < ε := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  have hfC : MemLp (fun x => (f x : ℂ)) p γ := hf.ofReal
  have hd : Dense (LinearMap.range (gaussianPolynomialLp (n := n) ℂ p hptop) :
      Set (Lp ℂ p γ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (gaussianPolynomialLp_closure_eq_top p hptop)
  intro ε hε
  obtain ⟨_, ⟨P, rfl⟩, hP⟩ := EMetric.mem_closure_iff.mp (hd (hfC.toLp _)) ε hε
  change edist (hfC.toLp _) ((memLp_eval_gaussian P hptop).toLp _) < ε at hP
  rw [Lp.edist_toLp_toLp] at hP
  obtain ⟨Q, hQ⟩ := exists_real_polynomial_re P
  refine ⟨Q, lt_of_le_of_lt (eLpNorm_mono_ae ?_) hP⟩
  filter_upwards [] with x
  change ‖f x - MvPolynomial.eval x Q‖ ≤
    ‖(f x : ℂ) - MvPolynomial.eval (fun i => (x i : ℂ)) P‖
  rw [hQ x]
  simpa only [Real.norm_eq_abs, Complex.sub_re, Complex.ofReal_re] using
    Complex.abs_re_le_norm ((f x : ℂ) - MvPolynomial.eval (fun i => (x i : ℂ)) P)

/-- The two-function Gaussian hypercontractive inequality bounds the correlated
integral by the `(1+r)` and `(1+s)` norms. [OD14, §11.1, Gaussian Hypercontractivity]
The joint integrability conclusion makes the expectation's domain explicit.

**Proof sketch.** Transfer the Boolean inequality to continuous compact
approximants through normalized correlated blocks. Lp approximation and Fatou's
argument give the absolute-product bound and integrability. At correlation zero,
independence and the bound for the mean handle the exponent-one endpoints. -/
theorem gaussian_hypercontractive_two_function (r s ρ : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r * s ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρ : ρ ^ 2 ≤ r * s)
    {f g : (Fin n → ℝ) → ℝ}
    (hf : MemLp f (ENNReal.ofReal (1 + r)) γ)
    (hg : MemLp g (ENNReal.ofReal (1 + s)) γ) :
    Integrable (fun z => f z.1 * g z.2) (correlatedGaussianMeasure ρ) ∧
      |∫ z, f z.1 * g z.2 ∂correlatedGaussianMeasure ρ| ≤
        (eLpNorm f (ENNReal.ofReal (1 + r)) γ).toReal *
          (eLpNorm g (ENNReal.ofReal (1 + s)) γ).toReal := by
  have hp : 1 ≤ ENNReal.ofReal (1 + r) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hq : 1 ≤ ENNReal.ofReal (1 + s) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  by_cases hzero : ρ = 0
  · subst ρ
    rw [correlatedGaussianMeasure_zero]
    refine ⟨(hf.integrable hp).mul_prod (hg.integrable hq), ?_⟩
    rw [integral_prod_mul f g, abs_mul]
    exact mul_le_mul (norm_integral_le_toReal_eLpNorm γ _ hp hf)
      (norm_integral_le_toReal_eLpNorm γ _ hq hg) (abs_nonneg _) ENNReal.toReal_nonneg
  · have hrpos : 0 < r := by nlinarith [sq_pos_of_ne_zero hzero]
    have hspos : 0 < s := by nlinarith [sq_pos_of_ne_zero hzero]
    obtain ⟨hi, hb⟩ := gaussian_two_function_positiveOffsets r s ρ hrpos hspos hrs
      hρ0 hρ1 hρ ⟨measurable_fst, correlatedGaussianMeasure_fst ρ⟩
      ⟨measurable_snd, correlatedGaussianMeasure_snd ⟨by linarith, hρ1⟩⟩ hf hg
    refine ⟨hi, abs_integral_le_integral_abs.trans ?_⟩
    simpa only [abs_mul] using hb

/-- Gaussian noise contracts from Lp to Lq at the sharp correlation threshold.
[OD14, Thm. 11.23] Extended exponents also express the constant-output `p=1`
and `q=∞` endpoints, using `0 * ∞ = 0`.

**Proof sketch.** Equal exponents use ordinary contraction, and correlation zero
gives the Gaussian mean at every output exponent. In the remaining finite case,
the two-function estimate bounds all bounded dual tests. Truncated signed powers
then give Lq membership and the sharp norm bound. -/
theorem gaussian_hypercontractive (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ENNReal.ofReal (ρ ^ 2) * (q - 1) ≤ p - 1)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p γ) :
    MemLp (gaussianNoise ρ f) q γ ∧ eLpNorm (gaussianNoise ρ f) q γ ≤ eLpNorm f p γ := by
  have hc : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hρ1⟩
  by_cases heq : p = q
  · subst q
    exact ⟨gaussianNoise_memLp hc p hp hf, gaussianNoise_contract hc p hp hf⟩
  by_cases hz : ρ = 0
  · subst ρ
    rw [gaussianNoise_zero]
    refine ⟨memLp_const _, ?_⟩
    have hmean := norm_integral_le_toReal_eLpNorm γ p hp hf
    rw [eLpNorm_const _ (zero_lt_one.trans_le (hp.trans hpq)).ne' (by exact NeZero.ne γ)]
    simpa only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs] using
      (ENNReal.ofReal_le_iff_le_toReal hf.eLpNorm_lt_top.ne).mpr hmean
  · obtain ⟨hp1, hqfin⟩ := hypercontractive_exponents_of_nonzero hp
      (lt_of_le_of_ne hpq heq) ρ hz hρ
    have hpfin : p ≠ ⊤ := ne_top_of_le_ne_top hqfin hpq
    have hpr : 1 < p.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpfin).mpr hp1
    have hqr : 1 < q.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqfin).mpr (hp1.trans_le hpq)
    have hreal := hypercontractive_toReal_condition hp hpq hqfin ρ hρ
    have hfreal : MemLp f (ENNReal.ofReal p.toReal) γ := by
      simpa only [ENNReal.ofReal_toReal hpfin] using hf
    have htest (g : (Fin n → ℝ) → ℝ) (hg : MemLp g ⊤ γ) :
        |∫ x, gaussianNoise ρ f x * g x ∂γ| ≤ (eLpNorm f p γ).toReal *
          (eLpNorm g (ENNReal.ofReal (q.toReal / (q.toReal - 1))) γ).toReal := by
      simpa only [ENNReal.ofReal_toReal hpfin] using
        gaussianNoise_dual_test_bound p.toReal q.toReal ρ hpr
          (ENNReal.toReal_mono hqfin hpq) hρ0 hρ1 hreal
          ⟨measurable_fst, correlatedGaussianMeasure_fst ρ⟩
          ⟨measurable_snd, correlatedGaussianMeasure_snd hc⟩ hfreal hg
    have hfull := memLp_and_eLpNorm_le_of_bounded_pairing γ q.toReal hqr
      ((gaussianNoise_memLp hc p hp hf).integrable hp) (eLpNorm f p γ).toReal
      ENNReal.toReal_nonneg htest
    simpa only [ENNReal.ofReal_toReal hqfin,
      ENNReal.ofReal_toReal hf.eLpNorm_lt_top.ne] using hfull

end BooleanAnalysis.GaussianSpace
