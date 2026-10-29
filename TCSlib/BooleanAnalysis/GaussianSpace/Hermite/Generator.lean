/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Noise
import TCSlib.BooleanAnalysis.GaussianSpace.OrnsteinUhlenbeck
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Group.Tannery

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Gaussian generator in Hermite coordinates

## Main definitions

* `gaussianGeneratorMultiplier`: the scalar multiplier of a generator difference quotient.

## Main results

The positive Gaussian generator multiplies Hermite coefficients by total degree.
Its strong L² domain is described by square summability of the weighted spectrum.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Proposition 11.40 and Exercise 11.18.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- Nonnegative Gaussian semigroup times give admissible noise correlations. -/
lemma exp_neg_mem_correlationInterval {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · linarith [Real.exp_pos (-t)]
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)

/-- The scalar multiplier of a positive Gaussian generator difference quotient.
[OD14, Prop. 11.40; Ex. 11.18] -/
noncomputable def gaussianGeneratorMultiplier (d : ℕ) (t : ℝ) : ℝ :=
  (1 - (Real.exp (-t)) ^ d) / t

/-- The scalar generator difference-quotient multiplier tends to its degree as
time decreases to zero. [OD14, Prop. 11.40; Ex. 11.18]

**Proof sketch.** Differentiate the exponential degree multiplier at zero and
express its right derivative as the limit of its difference quotients. -/
lemma gaussianGeneratorMultiplier_tendsto (d : ℕ) :
    Tendsto (gaussianGeneratorMultiplier d) (𝓝[>] (0 : ℝ)) (𝓝 (d : ℝ)) := by
  have h : HasDerivAt (fun t : ℝ => 1 - (Real.exp (-t)) ^ d) (d : ℝ) 0 := by
    simpa [Function.comp_def] using
      ((((Real.hasDerivAt_exp (-(0 : ℝ))).comp 0
        (hasDerivAt_id (0 : ℝ)).neg).pow d).const_sub 1)
  unfold gaussianGeneratorMultiplier
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h.tendsto_slope_zero_right

/-- At positive times, the scalar generator quotient multiplier lies between
zero and its limiting degree. [OD14, Ex. 11.18]

**Proof sketch.** Write the exponential power as the exponential of degree times
time. Positivity gives the lower bound, and the tangent-line bound for the
exponential gives the upper bound. -/
lemma gaussianGeneratorMultiplier_bounds (d : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ gaussianGeneratorMultiplier d t ∧ gaussianGeneratorMultiplier d t ≤ (d : ℝ) := by
  unfold gaussianGeneratorMultiplier
  simp only [← Real.exp_nat_mul]
  have ha : (d : ℝ) * (-t) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) (neg_nonpos.mpr ht.le)
  constructor
  · exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr ha)) ht.le
  · apply (div_le_iff₀ ht).2
    have h := Real.add_one_le_exp ((d : ℝ) * (-t))
    nlinarith

/-- The squared error of a scalar generator multiplier is bounded by the
corresponding degree-weighted square. -/
private lemma gaussianGeneratorMultiplier_error_sq_le (d : ℕ) {t : ℝ}
    (ht : 0 < t) (c : ℝ) :
    ((gaussianGeneratorMultiplier d t - (d : ℝ)) * c) ^ 2 ≤ ((d : ℝ) * c) ^ 2 := by
  have hq := gaussianGeneratorMultiplier_bounds d ht
  have hs : (gaussianGeneratorMultiplier d t - (d : ℝ)) ^ 2 ≤ (d : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr hq.2),
      sq_nonneg (gaussianGeneratorMultiplier d t)]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_right hs (sq_nonneg c)

/-- Summable degree-weighted coefficients dominate the squared errors of the
scalar generator quotients, whose total tends to zero.
[OD14, Ex. 11.18] The formulation permits arbitrary degree-indexed coefficient
families to isolate the dominated-convergence argument.

**Proof sketch.** Each scalar multiplier tends to its degree. Its squared
error is bounded by the degree-weighted square, so dominated convergence for
summable families applies. -/
private lemma gaussianGeneratorMultiplier_error_tsum_tendsto {ι : Type*}
    (d : ι → ℕ) (c : ι → ℝ) (hc : Summable (fun i => ((d i : ℝ) * c i) ^ 2)) :
    Tendsto (fun t : ℝ =>
      ∑' i, ((gaussianGeneratorMultiplier (d i) t - (d i : ℝ)) * c i) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpoint (i : ι) :
      Tendsto (fun t : ℝ =>
        ((gaussianGeneratorMultiplier (d i) t - (d i : ℝ)) * c i) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using
      (((gaussianGeneratorMultiplier_tendsto (d i)).sub_const (d i : ℝ)).mul_const
        (c i)).pow 2
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ i : ι,
      ‖((gaussianGeneratorMultiplier (d i) t - (d i : ℝ)) * c i) ^ 2‖ ≤
        ((d i : ℝ) * c i) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact gaussianGeneratorMultiplier_error_sq_le (d i) ht (c i)
  simpa only [tsum_zero] using
    (tendsto_tsum_of_dominated_convergence
      (f := fun (t : ℝ) (i : ι) =>
        ((gaussianGeneratorMultiplier (d i) t - (d i : ℝ)) * c i) ^ 2)
      (g := fun _ : ι => (0 : ℝ)) hc hpoint hbound)

/-- A nonnegative-time Gaussian generator difference quotient belongs to L².
At time zero, totalized division makes the quotient identically zero.

**Proof sketch.** Gaussian noise preserves L² at the admissible correlation.
Subtraction and multiplication by a fixed scalar preserve membership. -/
lemma memLp_gaussianGeneratorQuotient (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t) 2 γ := by
  convert (hf.sub (gaussianNoise_memLp (exp_neg_mem_correlationInterval ht)
    2 (by norm_num) hf)).const_smul t⁻¹ using 1
  ext x
  simp [div_eq_mul_inv, mul_comm]

/-- The Hermite coefficient of a positive-time generator difference quotient is
the original coefficient times its degree multiplier. [OD14, Prop. 11.40]

**Proof sketch.** Use coefficient subtraction and scalar compatibility, then
insert the Gaussian noise coefficient multiplier. -/
lemma hermiteCoeff_gaussianGeneratorQuotient (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (t : ℝ) (ht : 0 < t) (α : Fin n → ℕ) :
    hermiteCoeff (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t) α =
      gaussianGeneratorMultiplier (∑ i, α i) t * hermiteCoeff f α := by
  have hρ := exp_neg_mem_correlationInterval ht.le
  simp only [div_eq_mul_inv, ← mul_comm t⁻¹]
  rw [hermiteCoeff_const_mul,
    hermiteCoeff_sub f (gaussianNoise (Real.exp (-t)) f) hf
      (gaussianNoise_memLp hρ 2 (by norm_num) hf) α,
    hermiteCoeff_gaussianNoise f hf (Real.exp (-t)) hρ α]
  unfold gaussianGeneratorMultiplier
  ring

/-- The positive Gaussian generator multiplies Hermite coefficients by degree.
[OD14, Prop. 11.40] **Proof sketch.** Pair its strong difference quotients with
a Hermite function and differentiate the scalar correlation eigenvalue. -/
theorem hermiteCoeff_gaussianGenerator (f g : (Fin n → ℝ) → ℝ)
    (hfg : HasGaussianGenerator f g) (α : Fin n → ℕ) :
    hermiteCoeff g α = ((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t :=
    self_mem_nhdsWithin
  have hlim := tendsto_hermiteCoeff_of_eLpNorm_sub_tendsto
    (fun t x => (f x - gaussianNoise (Real.exp (-t)) f x) / t)
    g hfg.2.1
    (by
      filter_upwards [hpos] with t ht
      exact memLp_gaussianGeneratorQuotient f hfg.1 t ht.le)
    hfg.2.2 α
  refine tendsto_nhds_unique hlim ?_
  refine ((gaussianGeneratorMultiplier_tendsto (∑ i, α i)).mul_const
    (hermiteCoeff f α)).congr' ?_
  filter_upwards [hpos] with t ht
  exact (hermiteCoeff_gaussianGeneratorQuotient f hfg.1 t ht α).symm

/-- The strong generator has the degree-weighted Hermite expansion in L².
[OD14, Prop. 11.40] **Proof sketch.** Expand the generator output in the Hermite
basis and replace its coefficients using the preceding multiplier formula. -/
theorem gaussianGenerator_hermite_expansion (f g : (Fin n → ℝ) → ℝ)
    (hfg : HasGaussianGenerator f g) :
    HasSum (fun α : Fin n → ℕ =>
      (((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α) • hermiteL2 α)
      (hfg.2.1.toLp g) := by
  simpa only [hermiteCoeff_gaussianGenerator f g hfg] using
    hermite_expansion g hfg.2.1

/-- Two Gaussian L² functions satisfy the strong generator relation when their
Hermite coefficients differ by multiplication by total degree.
[OD14, Prop. 11.40; Ex. 11.18]

**Proof sketch.** Compute the difference-quotient error coefficients. Their
squared sum tends to zero by the scalar dominated-convergence estimate. Parseval's
norm formula then gives the required strong Gaussian L² limit. -/
lemma hasGaussianGenerator_of_hermiteCoeff (f g : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) (hg : MemLp g 2 γ)
    (hcoeff : ∀ α : Fin n → ℕ,
      hermiteCoeff g α = ((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α) :
    HasGaussianGenerator f g := by
  have hsum : Summable (fun α : Fin n → ℕ =>
      (((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α) ^ 2) := by
    simpa only [hcoeff] using hermiteCoeff_sq_summable g hg
  have hlim := gaussianGeneratorMultiplier_error_tsum_tendsto
    (fun α : Fin n → ℕ => ∑ i, α i) (hermiteCoeff f) hsum
  have hnorm := ENNReal.tendsto_ofReal hlim.sqrt
  simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at hnorm
  refine ⟨hf, hg, hnorm.congr' ?_⟩
  filter_upwards
    [show ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin] with t ht
  rw [eLpNorm_two_eq_sqrt_hermiteCoeff
    (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x)
    (by simpa only [Pi.sub_apply] using
      (memLp_gaussianGeneratorQuotient f hf t ht.le).sub hg)]
  simp_rw [hermiteCoeff_sub _ _
    (memLp_gaussianGeneratorQuotient f hf t ht.le) hg,
    hermiteCoeff_gaussianGeneratorQuotient f hf t ht, hcoeff, sub_mul]

/-- A Gaussian L² function is in the generator domain exactly when its Hermite
coefficients weighted by degree are square summable.
[OD14, Prop. 11.40; Ex. 11.18]

**Proof sketch.** Necessity is Parseval for the generator. Conversely the
degree-weighted series defines an L² output, and dominated convergence proves
the required strong convergence of the noise difference quotients. -/
theorem gaussianGeneratorDomain_iff_hermite (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 γ) :
    InGaussianGeneratorDomain f ↔ Summable (fun α : Fin n → ℕ =>
      (((∑ i, α i : ℕ) : ℝ) ^ 2) * (hermiteCoeff f α) ^ 2) := by
  constructor
  · rintro ⟨g, hfg⟩
    simpa only [hermiteCoeff_gaussianGenerator f g hfg, mul_pow] using
      hermiteCoeff_sq_summable g hfg.2.1
  · intro hc
    obtain ⟨g, hg, hcoeff⟩ := exists_memLp_hermiteCoeff
      (fun α : Fin n → ℕ => ((∑ i, α i : ℕ) : ℝ) * hermiteCoeff f α)
      (by simpa only [mul_pow] using hc)
    exact ⟨g, hasGaussianGenerator_of_hermiteCoeff f g hf hg
      (fun α => congrFun hcoeff α)⟩

end BooleanAnalysis.GaussianSpace
