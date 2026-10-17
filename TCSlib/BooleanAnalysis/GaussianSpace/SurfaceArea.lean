/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Halfspace
import TCSlib.BooleanAnalysis.GaussianSpace.IndicatorSmoothing
import TCSlib.BooleanAnalysis.GaussianSpace.IndicatorRegularity
import TCSlib.BooleanAnalysis.GaussianSpace.SmoothVariation
import TCSlib.BooleanAnalysis.GaussianSpace.GaussianBobkov
import TCSlib.BooleanAnalysis.GaussianSpace.ProfileApproximation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian surface area from infinitesimal rotation sensitivity

## Main definitions

`gaussianSurfaceArea` is the extended nonnegative lower-limit definition in `Definitions`.

## Main results

* `surfaceArea_rotation_limit`: the defining lower limit is a right limit.
* `surfaceArea_congr_ae`: null modifications do not change surface area.
* `surfaceArea_halfspace`: a unit-normal halfspace has surface area `φ(t)`.
* `rotationSensitivity_le_surfaceArea`: Theorem 11.51.
* `surfaceArea_volume_lower_bound`: Theorem 11.52.
* `gaussian_isoperimetric`: the general-volume Gaussian isoperimetric lower bound.

Smooth-relaxation and Minkowski-content identifications are deferred in
`COVERAGE.md`, rather than asserted with unspecified
regularity hypotheses. No frontier-Hausdorff perimeter or convex upper bound is duplicated.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Definition 11.48, Proposition 11.49,
  Theorems 11.51–11.52, and the Gaussian Isoperimetric Inequality.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ} {A B : Set (Fin n → ℝ)}

/-- Every positive secant slope of a continuous subadditive function vanishing at
zero is bounded by the extended lower limit of its slopes at zero.

**Proof sketch.** Write the fixed positive argument as an integer multiple of a
small step plus a remainder smaller than that step. Subadditivity bounds its
value by the sum over the equal steps and the remainder. Continuity makes the
remainder negligible, so every slope below the fixed slope eventually bounds the
small-step slopes from below. -/
private lemma subadditive_quotient_le_liminf {f : ℝ → ℝ}
    (hzero : f 0 = 0) (hcont : ContinuousAt f 0)
    (hadd : ∀ s t, f (s + t) ≤ f s + f t) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (f δ / δ) ≤
      liminf (fun t : ℝ => ENNReal.ofReal (f t / t)) (𝓝[>] (0 : ℝ)) := by
  refine (le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mpr fun b hb => ?_
  have hb' : b.toReal * δ < f δ :=
    (lt_div_iff₀ hδ).mp (ENNReal.toReal_lt_of_lt_ofReal hb)
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually (gt_mem_nhds (show f 0 < f δ - b.toReal * δ by
      rw [hzero]
      linarith)))
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  let k := ⌊δ / t⌋₊
  have hkt : (k : ℝ) * t ≤ δ :=
    (le_div_iff₀ ht.1).mp (Nat.floor_le (div_nonneg hδ.le ht.1.le))
  have hrem : δ - (k : ℝ) * t < t := by
    have := (div_lt_iff₀ ht.1).mp (Nat.lt_floor_add_one (δ / t))
    dsimp [k]
    nlinarith
  have hrsmall : f (δ - (k : ℝ) * t) < f δ - b.toReal * δ :=
    hsmall (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (sub_nonneg.mpr hkt)]
      using hrem.trans ht.2)
  have hsum : f ((k : ℝ) * t) ≤ (k : ℝ) * f t := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.le_sum_of_subadditive f hzero.le hadd Finset.univ (fun _ : Fin k => t)
  apply (ENNReal.lt_ofReal_iff_toReal_lt hb.ne_top).mpr
  apply (lt_div_iff₀ ht.1).mpr
  by_contra h
  have hmul : (k : ℝ) * f t ≤ b.toReal * δ :=
    (mul_le_mul_of_nonneg_left (le_of_not_gt h) (Nat.cast_nonneg k)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hkt (ENNReal.toReal_nonneg (a := b))])
  have := hadd ((k : ℝ) * t) (δ - (k : ℝ) * t)
  rw [add_sub_cancel] at this
  linarith

/-- Scaled rotation sensitivity at a positive angle is bounded by its defining
lower limit, by continuity at zero and subadditivity. -/
private lemma rotationSensitivity_quotient_le_surfaceArea (hA : MeasurableSet A)
    {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (Real.sqrt (Real.pi / 2) * rotationSensitivity A δ / δ) ≤
      gaussianSurfaceArea A := by
  apply subadditive_quotient_le_liminf
    (f := fun θ => Real.sqrt (Real.pi / 2) * rotationSensitivity A θ) ?_ ?_ ?_ hδ
  · simp [rotationSensitivity]
  · have hcont : ContinuousAt (rotationSensitivity A) 0 := by
      simpa [ContinuousAt, rotationSensitivity] using rotationSensitivity_tendsto_zero hA
    exact hcont.const_mul _
  · intro s t
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (rotationSensitivity_subadditive hA s t)
      (Real.sqrt_nonneg _)


/-- The scaled rotation-sensitivity quotient has a right limit in `[0,∞]`, equal
to the Gaussian surface area, including the case of infinite surface area.
[OD14, Def. 11.48; equation (11.14)]

**Proof sketch.** Gaussian rotation sensitivity is continuous at angle zero and
subadditive. Decompose a fixed angle into equal small steps and a remainder;
continuity makes the remainder negligible. Every positive-angle quotient is
therefore bounded by the lower limit at zero. This also bounds the upper limit
by the lower limit and gives convergence, even when the lower limit is infinite. -/
theorem surfaceArea_rotation_limit (hA : MeasurableSet A) :
    Tendsto (fun θ : ℝ =>
      ENNReal.ofReal (Real.sqrt (Real.pi / 2) * rotationSensitivity A θ / θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (gaussianSurfaceArea A)) :=
  by
    apply tendsto_of_le_liminf_of_limsup_le le_rfl
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact rotationSensitivity_quotient_le_surfaceArea hA hθ

/-- Null changes under Gaussian measure leave every rotation sensitivity unchanged.
[OD14, §11.4, discussion before Def. 11.48]

**Proof sketch.** Both endpoints have the standard Gaussian law. Pull the
almost-everywhere membership equivalence back along each endpoint and compare
the disagreement events. -/
lemma rotationSensitivity_congr_ae
    (hAB : ∀ᵐ z ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure), z ∈ A ↔ z ∈ B)
    (θ : ℝ) : rotationSensitivity A θ = rotationSensitivity B θ := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => standardGaussianMeasure
  have hf : ∀ᵐ z ∂(μ.prod μ), z.1 ∈ A ↔ z.1 ∈ B :=
    measurePreserving_fst.quasiMeasurePreserving.ae hAB
  have hr := (measurePreserving_gaussianRotation (n := n) θ).quasiMeasurePreserving.ae hf
  unfold rotationSensitivity
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hf, hr] with z hz hrot
  change ((fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) ∈ A ↔
    (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) ∈ B) at hrot
  apply propext
  change (¬ (z.1 ∈ A ↔
      (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) ∈ A)) ↔
    (¬ (z.1 ∈ B ↔
      (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) ∈ B))
  tauto

/-- Measurable sets that agree almost everywhere under Gaussian measure have the
same rotation-limit surface area. [OD14, §11.4, discussion before Def. 11.48]

**Proof sketch.** Both endpoints of a Gaussian rotation have the standard Gaussian
law, so null changes at either endpoint leave every disagreement probability
unchanged. Their scaled lower limits therefore agree. -/
lemma surfaceArea_congr_ae (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ z ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure), z ∈ A ↔ z ∈ B) :
    gaussianSurfaceArea A = gaussianSurfaceArea B :=
  by
    simp only [gaussianSurfaceArea, rotationSensitivity_congr_ae hAB]

/-- A closed halfspace with unit normal and threshold `t` has Gaussian surface area
`φ(t)`. This is Proposition 11.49 with the threshold explicit instead of the volume:
the volume is `Φ(t)`, so `φ(t) = U(Φ(t))`. [OD14, Prop. 11.49]

**Proof sketch.** Project onto the unit normal, obtaining a pair of independent
scalar Gaussians. Condition on the second coordinate and differentiate the
resulting Gaussian CDF increment. Dominated convergence and the first absolute
Gaussian moment give the normalized limit, hence its defining lower limit. -/
theorem surfaceArea_halfspace (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1) (t : ℝ) :
    gaussianSurfaceArea {z : Fin n → ℝ | ∑ i, a i * z i ≤ t} =
      ENNReal.ofReal (standardGaussianPDF t) :=
  by
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      (halfspace_rotation_quotient_tendsto a ha t)).liminf_eq

/-- At every positive angle, scaled rotation sensitivity is bounded by Gaussian
surface area. [OD14, Thm. 11.51]

**Proof sketch.** Decompose the fixed angle into equal small steps and a remainder
smaller than one step. Subadditivity bounds the fixed-angle sensitivity by the
step sensitivities and the remainder. Continuity at zero makes the remainder
negligible, giving the bound by the defining extended lower limit. -/
theorem rotationSensitivity_le_surfaceArea (hA : MeasurableSet A) (δ : ℝ) (hδ : 0 < δ) :
    ENNReal.ofReal (Real.sqrt (Real.pi / 2) * rotationSensitivity A δ / δ) ≤
      gaussianSurfaceArea A :=
  by
    exact rotationSensitivity_quotient_le_surfaceArea hA hδ

/-- A set of Gaussian volume `α` has surface area at least `2 sqrt(2/π) α(1-α)`.
In particular this is sharp at volume one half. [OD14, Thm. 11.52]

**Proof sketch.** Apply the angle-to-surface-area bound at angle `π/2`. The
endpoints are independent, and their disagreement probability is `2α(1-α)`.
Simplify the prefactor. -/
theorem surfaceArea_volume_lower_bound (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * Real.sqrt (2 / Real.pi) *
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal *
      (1 - ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal)) ≤
      gaussianSurfaceArea A :=
  by
    convert rotationSensitivity_le_surfaceArea hA (Real.pi / 2) (by positivity) using 1
    rw [rotationSensitivity_pi_div_two hA]
    congr 1
    rw [mul_div_right_comm, Real.sqrt_div_self, ← Real.sqrt_inv, inv_div]
    ring

/-- A smooth unit-interval function whose integral rotation variation is
bounded by that of a measurable set has integral gradient length at most the
set's Gaussian surface area. [OD14, §11.4, Def. 11.48, smooth surface-area argument]
The conclusion uses a nonnegative extended integral, so no finite-area
assumption is required.

**Proof sketch.** Every normalized positive-angle rotation variation of the
function is bounded by the corresponding set variation, which is at most
surface area. Apply the smooth rotation/Fatou gradient bound. -/
theorem lintegral_gradient_le_surfaceArea_of_variation_le
    (hA : MeasurableSet A) {f : (Fin n → ℝ) → ℝ}
    {D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (D x) x) (hD : Continuous D)
    (hunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hvariation : ∀ θ : ℝ,
      (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
        |f z.1 - f (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i)|
        ∂((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
          (Measure.pi fun _ : Fin n => standardGaussianMeasure))) ≤ rotationSensitivity A θ) :
    (∫⁻ x : Fin n → ℝ,
      ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (D x (Pi.single i 1)) ^ 2))
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) ≤ gaussianSurfaceArea A := by
  apply lintegral_gaussianGradient_le_of_integral_variation_le hf hD hunit
  intro θ hθ
  refine (ENNReal.ofReal_le_ofReal ?_).trans (rotationSensitivity_le_surfaceArea hA θ hθ)
  apply div_le_div_of_nonneg_right _ hθ.le
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  simpa only [abs_sub_comm] using hvariation θ

/-- The averaged-indicator profile error can be removed from an extended
surface-area bound by taking the smoothing angle to zero.
[OD14, §11.4, smooth indicator approximation]

**Proof sketch.** The integral profile tends to zero. Embed it in the
nonnegative extended reals and add the fixed surface area, preserving the
limit even when that area is infinite. Pass the assumed inequalities to
this limit and use the interior profile formula. -/
private lemma isoperimetric_of_averaged_profile_bound {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hbound : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ENNReal.ofReal (closedGaussianProfile α) ≤
        ENNReal.ofReal (∫ x : Fin n → ℝ,
          closedGaussianProfile (averagedGaussianIndicator A u x)
          ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) + gaussianSurfaceArea A) :
    ENNReal.ofReal (gaussianIsoperimetric α) ≤ gaussianSurfaceArea A := by
  have hprof : Tendsto (fun u : ℝ => ∫ x : Fin n → ℝ,
      closedGaussianProfile (averagedGaussianIndicator A u x)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_integral_profile_averagedGaussianIndicator hA).mono_left nhdsWithin_le_nhds
  have hlim := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hprof
  have hright := hlim.add_const (gaussianSurfaceArea A)
  simp only [ENNReal.ofReal_zero, zero_add] at hright
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hright
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by positivity)] with u hu
  simpa only [closedGaussianProfile, if_pos hα] using hbound u hu

/-- Bounded Lipschitz derivative families for the averaged indicators suffice
for the isoperimetric lower bound. [OD14, §11.4, smooth indicator approximation]

**Proof sketch.** Apply the additive Gaussian Bobkov bound at each positive
smoothing angle. Its mean is the set's volume. Rotation-variation contraction
bounds the nonnegative integral gradient length by surface area. Genuine
gradient integrability permits the real-to-extended integral comparison;
the vanishing profile term then gives the desired bound. Derivative bounds
are needed separately at each angle, with no uniformity at angle zero. -/
private lemma gaussian_isoperimetric_of_averagedRegularity {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hvol : ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal = α)
    (hreg : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∃ (D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (C : ℝ≥0) (M : ℝ),
        (∀ x, HasFDerivAt (averagedGaussianIndicator A u) (D x) x) ∧
        LipschitzWith C D ∧ ∀ x, ‖D x‖ ≤ M) :
    ENNReal.ofReal (gaussianIsoperimetric α) ≤ gaussianSurfaceArea A := by
  apply isoperimetric_of_averaged_profile_bound hA hα
  intro u hu
  obtain ⟨D, C, M, hf, hD, hM⟩ := hreg u hu
  have hunit := averagedGaussianIndicator_mem_unitInterval hA u
  have hb := gaussian_bobkov_smooth_le_sum hunit hf hD M hM
  rw [integral_averagedGaussianIndicator hA u, measureReal_def, hvol] at hb
  refine (ENNReal.ofReal_le_ofReal hb).trans ?_
  rw [ENNReal.ofReal_add (integral_nonneg fun _ => closedGaussianProfile_nonneg _)
    (integral_nonneg fun _ => Real.sqrt_nonneg _)]
  apply add_le_add_left
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_gaussianGradient_of_bounded hD.continuous M hM)
    (Eventually.of_forall fun _ => Real.sqrt_nonneg _)]
  exact lintegral_gradient_le_surfaceArea_of_variation_le hA hf hD.continuous hunit
    (fun θ => averagedGaussianIndicator_rotation_variation_le hA u θ)

/-- A measurable set with Gaussian volume `α ∈ (0,1)` has surface area at least
the existing Gaussian isoperimetric profile `U(α)`.
[OD14, §11.4, Gaussian Isoperimetric Inequality]
The open-volume formulation uses the established interior quantile API; the
endpoint-volume inequalities are just nonnegativity of the extended surface area.

**Proof sketch.** Transfer Boolean Bobkov to smooth Gaussian functions by
normalized bit sums. Translated Gaussian density differentiation gives bounded
Lipschitz derivatives for averaged indicators at positive smoothing angles.
Apply Gaussian Bobkov to these averages. Averaging contracts rotation variation, and differentiation with Fatou's inequality bounds their
integral gradient norms by surface area. Integral approximation makes their
profile terms vanish, leaving the isoperimetric lower bound. -/
theorem gaussian_isoperimetric (hA : MeasurableSet A) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hvol : ((Measure.pi fun _ : Fin n => standardGaussianMeasure) A).toReal = α) :
    ENNReal.ofReal (gaussianIsoperimetric α) ≤ gaussianSurfaceArea A := by
  apply gaussian_isoperimetric_of_averagedRegularity hA hα hvol
  intro u hu
  have hsin : Real.sin u ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2, Real.pi_pos])).ne'
  refine ⟨fderiv ℝ (averagedGaussianIndicator A u),
    (n : ℝ≥0) ^ 2 * (2 / ⟨Real.sin u ^ 2, sq_nonneg _⟩),
    (n : ℝ) * (1 + 1 / (Real.sin u ^ 2)), ?_,
    lipschitzWith_fderiv_averagedGaussianIndicator hA u hsin,
    norm_fderiv_averagedGaussianIndicator_le hA u hsin⟩
  intro x
  exact (hasFDerivAt_averagedGaussianIndicator hA u hsin x).differentiableAt.hasFDerivAt

end BooleanAnalysis.GaussianSpace
