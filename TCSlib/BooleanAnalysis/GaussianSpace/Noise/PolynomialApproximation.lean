/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Polynomial
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Exponential
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Torus

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial approximation in Gaussian Lp

## Main definitions

* `gaussianPolynomialLp`: polynomial evaluation as a linear map into Gaussian Lp.

## Main results

Polynomial moment bounds, exponential Taylor approximation and compact-torus
Fourier approximation are combined in this module.

* `exp_linear_mem_gaussianPolynomial_closure`: linear exponential Lp classes
  are limits of polynomial classes.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Theorem 11.22.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Evaluate real or complex polynomials at real Gaussian vectors and take their
Lp classes. This map is linear in the polynomial coefficients. -/
noncomputable def gaussianPolynomialLp (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) (hp : p ≠ ⊤) : MvPolynomial (Fin n) 𝕜 →ₗ[𝕜] Lp 𝕜 p γ where
  toFun P := (memLp_eval_gaussian P hp).toLp _
  map_add' P Q := by
    simpa only [MvPolynomial.eval_add, Pi.add_apply] using
      (memLp_eval_gaussian P hp).toLp_add (memLp_eval_gaussian Q hp)
  map_smul' c P := by
    simpa only [MvPolynomial.smul_eval, Pi.smul_apply, smul_eq_mul] using
      (memLp_eval_gaussian P hp).toLp_const_smul c

/-- An Lp class represented by a complex linear exponential lies in the closure
of the Gaussian polynomial classes. [OD14, §11.1, proof of Thm. 11.22]

**Proof sketch.** Represent the linear form by a degree-one polynomial and form
its exponential Taylor polynomials. Their Gaussian Lp convergence puts the limit
in the closure of the polynomial range. -/
lemma exp_linear_mem_gaussianPolynomial_closure (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (L : (Fin n → ℝ) →L[ℝ] ℂ) (f : Lp ℂ p γ)
    (hf : f =ᵐ[γ] fun x => Complex.exp (L x)) :
    f ∈ (LinearMap.range (gaussianPolynomialLp (n := n) ℂ p hp)).topologicalClosure := by
  classical
  obtain ⟨Q, hQ⟩ := exists_polynomial_eval_linear L
  let P (k : ℕ) : MvPolynomial (Fin n) ℂ :=
    ∑ m ∈ Finset.range k, MvPolynomial.C ((m.factorial : ℂ)⁻¹) * Q ^ m
  have hP (k : ℕ) (x : Fin n → ℝ) :
      MvPolynomial.eval (fun i => (x i : ℂ)) (P k) =
        ∑ m ∈ Finset.range k, (L x) ^ m / m.factorial := by
    simp only [P, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_pow, hQ, div_eq_mul_inv, mul_comm]
  have hnorm (k : ℕ) :
      eLpNorm (⇑(gaussianPolynomialLp ℂ p hp (P k)) - ⇑f) p γ =
        eLpNorm (fun x => Complex.exp (L x) -
          ∑ m ∈ Finset.range k, (L x) ^ m / m.factorial) p γ := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [(memLp_eval_gaussian (P k) hp).coeFn_toLp, hf] with x hx hfx
    change ‖(memLp_eval_gaussian (P k) hp).toLp _ x - f x‖ = _
    rw [hx]
    change ‖MvPolynomial.eval (fun i => (x i : ℂ)) (P k) - f x‖ = _
    rw [hP k x, hfx, norm_sub_rev]
  have ht : Tendsto (fun k => gaussianPolynomialLp ℂ p hp (P k)) atTop (𝓝 f) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
    simp_rw [hnorm]
    exact tendsto_gaussian_exp_taylor L hp
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun k =>
    Set.mem_range_self (P k))

/-- Every Fourier monomial pulled back through the torus map is a Gaussian Lp
limit of polynomial evaluations. [OD14, §11.1, proof of Thm. 11.22]

**Proof sketch.** The pullback is a complex linear exponential. Apply its
Gaussian Taylor approximation. -/
lemma gaussianTorusFourier_mem_polynomial_closure (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (m : (Fin n × Bool) → ℤ) :
    gaussianTorusFourierLp γ p m ∈
      (LinearMap.range (gaussianPolynomialLp (n := n) ℂ p hp)).topologicalClosure := by
  let a (i : Fin n) : ℝ :=
    2 * Real.pi * ((m (i, false) : ℝ) + Real.sqrt 2 * (m (i, true) : ℝ))
  let L : (Fin n → ℝ) →L[ℝ] ℂ :=
    Complex.I • Complex.ofRealCLM.comp (∑ i, a i • ContinuousLinearMap.proj i)
  apply exp_linear_mem_gaussianPolynomial_closure p hp L
  filter_upwards [coeFn_gaussianTorusFourierLp γ p m] with x hx
  rw [hx, mFourier_gaussianTorusMap]
  congr 1
  simp [L, a, mul_comm]

/-- Complex polynomial evaluations span a dense subspace of finite Gaussian Lp.
[OD14, Thm. 11.22, complex-valued version]

**Proof sketch.** The polynomial closure contains each pulled-back Fourier
monomial, and those monomials already span a dense subspace. -/
lemma gaussianPolynomialLp_closure_eq_top (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (LinearMap.range (gaussianPolynomialLp (n := n) ℂ p hp)).topologicalClosure = ⊤ := by
  apply le_antisymm le_top
  rw [← span_gaussianTorusFourier_dense (n := n) γ p hp]
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro _ ⟨m, rfl⟩
  exact gaussianTorusFourier_mem_polynomial_closure p hp m

end BooleanAnalysis.GaussianSpace
