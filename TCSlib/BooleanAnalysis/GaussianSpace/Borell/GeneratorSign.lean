/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.GeneratorIntegration
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Fourier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Positivity of the profile-weighted Gaussian generator

## Main definitions

The Gaussian profile slopes and spatial first and second derivatives are reused.

## Main results

For a C2 function with clipped probability range and bounded derivatives,
the first-endpoint slope-weighted Ornstein–Uhlenbeck generator is integrable
and has nonnegative Gaussian integral.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
local instance {n : ℕ} (ρ : ℝ) : IsProbabilityMeasure (correlatedGaussianMeasure (n := n) ρ) := by
  rw [correlatedGaussianMeasure_eq]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Clipped probability range and bounded coordinate derivatives ensure
integrability of every term in the weighted Gaussian integration-by-parts
identity. [MN15, §2, regularized interpolation]

**Proof sketch.** The slope is bounded by one and its partial derivatives
are bounded on the compact clipped square. The product and curvature terms
are therefore bounded. The coordinate-weighted term is bounded by a multiple
of the first endpoint norm, whose Gaussian first moment is finite. -/
lemma integrable_profileSlope_generator_terms {n : ℕ} (ρ : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (i : Fin n) (u du ddu : (Fin n → ℝ) → ℝ)
    (hu : Continuous u) (hdu : Continuous du) (hddu : Continuous ddu)
    (hurange : ∀ x, u x ∈ Set.Icc δ (1 - δ)) {M K : ℝ}
    (hM : ∀ x, |du x| ≤ M) (hK : ∀ x, |ddu x| ≤ K) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1) (correlatedGaussianMeasure ρ) ∧
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2) * ddu z.1) (correlatedGaussianMeasure ρ) ∧
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      z.1 i * (gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1))
        (correlatedGaussianMeasure ρ) ∧
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) * (du z.1) ^ 2 +
        ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
          du z.1 * du z.2) (correlatedGaussianMeasure ρ) := by
  haveI : IsProbabilityMeasure (correlatedGaussianMeasure (n := n) ρ) := by
    rw [correlatedGaussianMeasure_eq]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hrange (x) : u x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hδ.trans_le (hurange x).1, by linarith [(hurange x).2]⟩
  have huc1 : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => u z.1) :=
    hu.comp continuous_fst
  have huc2 : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => u z.2) :=
    hu.comp continuous_snd
  have hs : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      ((differentiableAt_gaussianBivariateSlope ρ (p := (u z.1, u z.2)) ⟨hrange z.1,hrange z.2⟩).continuousAt.comp
        (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) => (u z.1, u z.2))
        (huc1.continuousAt.prodMk huc2.continuousAt)))
  have hsB (z : (Fin n → ℝ) × (Fin n → ℝ)) :
      |gaussianBivariateSlope ρ (u z.1) (u z.2)| ≤ 1 := by
    exact abs_le.mpr ⟨by
      exact (neg_nonpos.mpr zero_le_one).trans (standardGaussianCDF_pos _).le,
      (standardGaussianCDF_lt_one _).le⟩
  have hHB (z : (Fin n → ℝ) × (Fin n → ℝ)) :
      |gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1| ≤ M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hsB z) (abs_nonneg _)).trans (by simpa using hM z.1)
  have hLB (z : (Fin n → ℝ) × (Fin n → ℝ)) :
      |gaussianBivariateSlope ρ (u z.1) (u z.2) * ddu z.1| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hsB z) (abs_nonneg _)).trans (by simpa using hK z.1)
  have hHc := hs.mul (hdu.comp continuous_fst)
  have hLc := hs.mul (hddu.comp continuous_fst)
  have hXc := (show Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => z.1 i) by fun_prop).mul hHc
  have hH := Integrable.of_bound (μ := correlatedGaussianMeasure ρ) hHc.aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hHB z))
  have hL := Integrable.of_bound (μ := correlatedGaussianMeasure ρ) hLc.aestronglyMeasurable K
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hLB z))
  have hfst : MeasurePreserving (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
      (correlatedGaussianMeasure ρ) (Measure.pi fun _ => standardGaussianMeasure) :=
    ⟨measurable_fst, correlatedGaussianMeasure_fst ρ⟩
  have hnorm : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => ‖z.1‖)
      (correlatedGaussianMeasure ρ) :=
    hfst.integrable_comp_of_integrable (by simpa only [pow_one] using
      (integrable_gaussianPi_norm_pow (n := n) 1))
  have hX := (hnorm.mul_const M).mono' hXc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 i)
        (hHB z) (abs_nonneg _) (norm_nonneg _)))
  obtain ⟨C,hC⟩ := gaussianBivariateSlope_derivatives_bounded ρ hδ hρ
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (u 0) (hurange 0) (u 0) (hurange 0)).1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hc := continuous_gaussianBivariateSlope_deriv_comp ρ hρ
    (fun z : (Fin n → ℝ) × (Fin n → ℝ) => u z.1) (fun z => u z.2)
    huc1 huc2 (fun z => hrange z.1) (fun z => hrange z.2)
  have hCc := (hc.1.mul ((hdu.comp continuous_fst).pow 2)).add
    ((((continuous_const (y := ρ)).mul hc.2).mul (hdu.comp continuous_fst)).mul (hdu.comp continuous_snd))
  refine ⟨hH,hL,hX,Integrable.of_bound hCc.aestronglyMeasurable
    (C * M ^ 2 + |ρ| * C * M * M) (Filter.Eventually.of_forall (fun z => ?_))⟩
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |deriv (fun p => gaussianBivariateSlope ρ p (u z.2)) (u z.1) * (du z.1) ^ 2| +
        |ρ * deriv (fun p => gaussianBivariateSlope ρ (u z.1) p) (u z.2) *
          du z.1 * du z.2| := abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_pow]
      gcongr
      · exact (hC _ (hurange z.1) _ (hurange z.2)).1
      · exact hM z.1
      · exact (hC _ (hurange z.1) _ (hurange z.2)).2
      · exact hM z.1
      · exact hM z.2


/-- Every coordinate contribution of the slope-weighted first-endpoint
Gaussian generator is integrable and has nonnegative integral for positive
correlation. [MN15, §2, generator sign]

**Proof sketch.** Bound the coordinate first and second derivatives by the
operator-norm hypotheses. The integrability lemma permits Gaussian integration
by parts, which identifies the integral with minus the averaged curvature. -/
lemma integrable_nonneg_integral_profileSlope_coordinate_generator {n : ℕ} {ρ δ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hδ : 0 < δ)
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    (hrange : ∀ x, u x ∈ Set.Icc δ (1 - δ)) {M K : ℝ}
    (hM : ∀ x, ‖fderiv ℝ u x‖ ≤ M)
    (hK : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K) (i : Fin n) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2) *
      (fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1) -
        z.1 i * fderiv ℝ u z.1 (Pi.single i 1))) (correlatedGaussianMeasure ρ) ∧
    0 ≤ ∫ z, gaussianBivariateSlope ρ (u z.1) (u z.2) *
      (fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1) -
        z.1 i * fderiv ℝ u z.1 (Pi.single i 1)) ∂correlatedGaussianMeasure ρ := by
  let e : Fin n → ℝ := Pi.single i 1
  let du := fun x => fderiv ℝ u x e
  let ddu := fun x => fderiv ℝ (fderiv ℝ u) x e e
  have he : ‖e‖ = 1 := by simp [e, Pi.norm_single]
  have huc : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdf : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hd (x) := (hdf.differentiable le_rfl x).hasFDerivAt.clm_apply
    (hasFDerivAt_const e x)
  have hduc : Differentiable ℝ du := fun x => (hd x).differentiableAt
  have hdduc : Continuous ddu :=
    ((hdf.continuous_fderiv le_rfl).clm_apply continuous_const).clm_apply continuous_const
  have hduB (x) : |du x| ≤ M := by
    calc
      _ ≤ ‖fderiv ℝ u x‖ * ‖e‖ := (fderiv ℝ u x).le_opNorm e
      _ ≤ M := by simpa only [he, mul_one] using hM x
  have hdduB (x) : |ddu x| ≤ K := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ u) x e‖ * ‖e‖ := (fderiv ℝ (fderiv ℝ u) x e).le_opNorm e
      _ ≤ (‖fderiv ℝ (fderiv ℝ u) x‖ * ‖e‖) * ‖e‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ u) x).le_opNorm e) (norm_nonneg e)
      _ ≤ K := by simpa only [he, mul_one] using hK x
  have hcoord (x) : fderiv ℝ du x e = ddu x := by
    change fderiv ℝ (fun x => fderiv ℝ u x e) x e = _
    rw [(hd x).fderiv]
    simp [ddu]
  have hri (x) : u x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hδ.trans_le (hrange x).1, by linarith [(hrange x).2]⟩
  have hc : ρ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hρ.1],hρ.2⟩
  obtain ⟨hH,hL,hX,hC⟩ := integrable_profileSlope_generator_terms ρ hδ hc i u du ddu
    hu.continuous hduc.continuous hdduc hrange hduB hdduB
  have hid := integral_profileSlope_generator_first ρ i u du ddu huc hduc hri
    (fun x => rfl) hcoord hH hL hX hC
  refine ⟨?_, ?_⟩
  · exact (hL.sub hX).congr (Filter.Eventually.of_forall (fun z => by
      change gaussianBivariateSlope ρ (u z.1) (u z.2) * ddu z.1 -
        z.1 i * (gaussianBivariateSlope ρ (u z.1) (u z.2) * du z.1) = _
      ring))
  · change 0 ≤ ∫ z, gaussianBivariateSlope ρ (u z.1) (u z.2) *
      (ddu z.1 - z.1 i * du z.1) ∂correlatedGaussianMeasure ρ
    rw [hid]
    exact neg_nonneg.mpr (integral_profileSlope_curvature_nonpos hρ u du hri hC)

/-- The slope-weighted first-endpoint Ornstein–Uhlenbeck generator of a
clipped C2 function with bounded derivatives is integrable and has nonnegative
Gaussian expectation for positive correlation. [MN15, §2, interpolation sign]

**Proof sketch.** Expand the derivative evaluated on the starting point in
coordinate directions. The generator is then the finite sum of coordinate
generators. Each weighted coordinate contribution is integrable with
nonnegative integral, so their sum has the same properties. -/
lemma integrable_nonneg_integral_profileSlope_generator {n : ℕ} {ρ δ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hδ : 0 < δ)
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    (hrange : ∀ x, u x ∈ Set.Icc δ (1 - δ)) {M K : ℝ}
    (hM : ∀ x, ‖fderiv ℝ u x‖ ≤ M)
    (hK : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2) *
      ((∑ i, fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1)) -
        fderiv ℝ u z.1 z.1)) (correlatedGaussianMeasure ρ) ∧
    0 ≤ ∫ z, gaussianBivariateSlope ρ (u z.1) (u z.2) *
      ((∑ i, fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1)) -
        fderiv ℝ u z.1 z.1) ∂correlatedGaussianMeasure ρ := by
  let F (i : Fin n) (z : (Fin n → ℝ) × (Fin n → ℝ)) :=
    gaussianBivariateSlope ρ (u z.1) (u z.2) *
      (fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1) -
        z.1 i * fderiv ℝ u z.1 (Pi.single i 1))
  have hi (i : Fin n) : Integrable (F i) (correlatedGaussianMeasure ρ) ∧
      0 ≤ ∫ z, F i z ∂correlatedGaussianMeasure ρ :=
    integrable_nonneg_integral_profileSlope_coordinate_generator hρ hδ hu hrange hM hK i
  have heq (z : (Fin n → ℝ) × (Fin n → ℝ)) :
      (∑ i, F i z) = gaussianBivariateSlope ρ (u z.1) (u z.2) *
      ((∑ i, fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1)) -
        fderiv ℝ u z.1 z.1) := by
    rw [realLinearFunctional_pi]
    simp only [F, Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · exact (integrable_finset_sum Finset.univ (fun i _ => (hi i).1)).congr
      (Filter.Eventually.of_forall heq)
  · calc
      _ = ∫ z, ∑ i, F i z ∂correlatedGaussianMeasure ρ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun z => (heq z).symm))
      _ = ∑ i, ∫ z, F i z ∂correlatedGaussianMeasure ρ :=
        integral_finset_sum Finset.univ (fun i _ => (hi i).1)
      _ ≥ 0 := Finset.sum_nonneg (fun i _ => (hi i).2)


/-- For a clipped C2 function with bounded derivatives, the sum of the two
profile-slope-weighted Ornstein–Uhlenbeck generators is integrable and has
nonnegative Gaussian expectation at positive correlation.
[MN15, §2, interpolation derivative sign]

**Proof sketch.** The first-endpoint weighted generator is integrable with
nonnegative expectation. Swapping the endpoints preserves the correlated
Gaussian law and turns it into the second-endpoint contribution. Sum the
two integrals. -/

lemma integrable_nonneg_integral_bivariate_generator {n : ℕ} {ρ δ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hδ : 0 < δ)
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    (hrange : ∀ x, u x ∈ Set.Icc δ (1 - δ)) {M K : ℝ}
    (hM : ∀ x, ‖fderiv ℝ u x‖ ≤ M)
    (hK : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      gaussianBivariateSlope ρ (u z.1) (u z.2) *
        ((∑ i, fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1)) -
          fderiv ℝ u z.1 z.1) +
      gaussianBivariateSlope ρ (u z.2) (u z.1) *
        ((∑ i, fderiv ℝ (fderiv ℝ u) z.2 (Pi.single i 1) (Pi.single i 1)) -
          fderiv ℝ u z.2 z.2)) (correlatedGaussianMeasure ρ) ∧
    0 ≤ ∫ z, gaussianBivariateSlope ρ (u z.1) (u z.2) *
        ((∑ i, fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1)) -
          fderiv ℝ u z.1 z.1) +
      gaussianBivariateSlope ρ (u z.2) (u z.1) *
        ((∑ i, fderiv ℝ (fderiv ℝ u) z.2 (Pi.single i 1) (Pi.single i 1)) -
          fderiv ℝ u z.2 z.2) ∂correlatedGaussianMeasure ρ := by
  let F : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun z =>
    gaussianBivariateSlope ρ (u z.1) (u z.2) *
      ((∑ i, fderiv ℝ (fderiv ℝ u) z.1 (Pi.single i 1) (Pi.single i 1)) -
        fderiv ℝ u z.1 z.1)
  have hF : Integrable F (correlatedGaussianMeasure ρ) ∧
      0 ≤ ∫ z, F z ∂correlatedGaussianMeasure ρ :=
    integrable_nonneg_integral_profileSlope_generator hρ hδ hu hrange hM hK
  have hp : MeasurePreserving (Prod.swap :
      ((Fin n → ℝ) × (Fin n → ℝ)) → ((Fin n → ℝ) × (Fin n → ℝ)))
      (correlatedGaussianMeasure ρ) (correlatedGaussianMeasure ρ) :=
    ⟨measurable_swap, correlatedGaussianMeasure_swap ⟨by linarith [hρ.1],hρ.2.le⟩⟩
  have hFi : Integrable (fun z => F z.swap) (correlatedGaussianMeasure ρ) :=
    hp.integrable_comp_of_integrable hF.1
  have hEq : (∫ z, F z.swap ∂correlatedGaussianMeasure ρ) =
      ∫ z, F z ∂correlatedGaussianMeasure ρ :=
    hp.integral_comp MeasurableEquiv.prodComm.measurableEmbedding F
  change Integrable (fun z => F z + F z.swap) (correlatedGaussianMeasure ρ) ∧
    0 ≤ ∫ z, F z + F z.swap ∂correlatedGaussianMeasure ρ
  refine ⟨hF.1.add hFi, ?_⟩
  rw [integral_add hF.1 hFi, hEq]
  exact add_nonneg hF.2 hF.2


end BooleanAnalysis.GaussianSpace
