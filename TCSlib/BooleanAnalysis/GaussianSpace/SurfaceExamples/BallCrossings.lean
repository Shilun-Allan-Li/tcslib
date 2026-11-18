/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.RadialGaussian
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Linear
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Radial representation of Gaussian ball crossings

## Main definitions

Crossing events are written with the existing Gaussian law and Euclidean norm.

## Main results

* `ball_sensitivity_radial`: the scalar radial representation of ball sensitivity.
* `scalar_q_measurable`: measurability of the conditional radial integral.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Example 11.50 and Exercise 11.17.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace BooleanAnalysis.GaussianSpace.BallCrossings

open ThresholdFunctions

variable {n : ℕ}

local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Rotation sensitivity equals the symmetric half-angle crossing probability.

**Proof sketch.** Pull the disagreement event back by rotation through minus half the angle; Gaussian rotation invariance preserves its probability. -/
private lemma half_angle {n : ℕ} (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) (t : ℝ) :
    rotationSensitivity A t =
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure)).real
      {z | ¬ ((fun i => Real.cos (t/2) * z.1 i - Real.sin (t/2) * z.2 i) ∈ A ↔
              (fun i => Real.cos (t/2) * z.1 i + Real.sin (t/2) * z.2 i) ∈ A)} := by
  let Event : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {z | ¬ (z.1 ∈ A ↔ (ContinuousLinearMap.rotation t z).1 ∈ A)}
  have hE : MeasurableSet Event := by
    convert ((hA.preimage measurable_fst).symmDiff
      (hA.preimage (measurable_fst.comp (ContinuousLinearMap.rotation t).continuous.measurable))) using 1
    ext z
    change (¬ (z.1 ∈ A ↔ (ContinuousLinearMap.rotation t z).1 ∈ A)) ↔ _
    simp only [Set.mem_symmDiff, Set.mem_preimage, Function.comp_apply]
    tauto
  rw [rotationSensitivity_eq]
  change _ = _
  calc
    _ = ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure)).real Event := by rfl
    _ = _ := by
      rw [← (measurePreserving_gaussianRotation (-t/2)).measureReal_preimage hE.nullMeasurableSet]
      congr 1
      ext z
      change (¬ ((ContinuousLinearMap.rotation (-t/2) z).1 ∈ A ↔
        (ContinuousLinearMap.rotation t (ContinuousLinearMap.rotation (-t/2) z)).1 ∈ A)) ↔ _
      rw [gaussianRotation_comp]
      have ht : -t/2+t=t/2 := by ring
      rw [ht]
      have hm : (ContinuousLinearMap.rotation (-t/2) z).1 =
          (fun i => Real.cos (t/2) * z.1 i - Real.sin (t/2) * z.2 i) := by
        ext i
        have hneg : -t/2= -(t/2) := by ring
        simp only [ContinuousLinearMap.rotation_apply, hneg, Real.cos_neg,
          Real.sin_neg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hm]
      rfl

/-- Applying a Euclidean isometry to the fixed vector preserves the integral of any function of the two endpoint norms.

**Proof sketch.** Change Gaussian variables by the same isometry, commute it through the linear combinations, and use preservation of norms. -/
private theorem radial_integral_coordinates_isometry (c s : ℝ) (W : E)
    (Q : E ≃ₗᵢ[ℝ] E) (F : ℝ → ℝ → ℝ) :
    (∫ V : Fin n → ℝ,
      F ‖c • Q W + s • WithLp.toLp 2 V‖
        ‖c • Q W - s • WithLp.toLp 2 V‖ ∂γ) =
    ∫ V : Fin n → ℝ,
      F ‖c • W + s • WithLp.toLp 2 V‖
        ‖c • W - s • WithLp.toLp 2 V‖ ∂γ := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let q := e.symm.trans (Q.toContinuousLinearEquiv.trans e)
  have h := (measurePreserving_gaussianIsometry Q).integral_comp
    q.toHomeomorph.measurableEmbedding
    (fun V : Fin n → ℝ =>
      F ‖c • Q W + s • WithLp.toLp 2 V‖
        ‖c • Q W - s • WithLp.toLp 2 V‖)
  change (∫ V : Fin n → ℝ,
      F ‖c • Q W + s • Q (WithLp.toLp 2 V)‖
        ‖c • Q W - s • Q (WithLp.toLp 2 V)‖ ∂γ) = _ at h
  simpa only [← map_smul, ← map_add, ← map_sub, Q.norm_map] using h.symm

/-- The Gaussian integral of a function of two symmetric endpoint norms depends only on the fixed vector norm.

**Proof sketch.** Reflection transports the fixed vector to the vector with the same norm in a chosen unit direction. Apply Gaussian isometry invariance. -/
private theorem radial_integral_coordinates (c s : ℝ) (W e₀ : E)
    (he₀ : ‖e₀‖ = 1) (F : ℝ → ℝ → ℝ) :
    (∫ V : Fin n → ℝ,
      F ‖c • W + s • WithLp.toLp 2 V‖
        ‖c • W - s • WithLp.toLp 2 V‖ ∂γ) =
    ∫ V : Fin n → ℝ,
      F ‖c • (‖W‖ • e₀) + s • WithLp.toLp 2 V‖
        ‖c • (‖W‖ • e₀) - s • WithLp.toLp 2 V‖ ∂γ := by
  have hn : ‖W‖ = ‖‖W‖ • e₀‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg W),
      he₀, mul_one]
  let Q := Submodule.reflection (ℝ ∙ (W - ‖W‖ • e₀))ᗮ
  have hQ : Q W = ‖W‖ • e₀ := Submodule.reflection_sub hn
  simpa only [hQ] using
    (radial_integral_coordinates_isometry c s W Q F).symm

/-- The symmetric ball crossing probability equals its iterated Gaussian indicator integral.

**Proof sketch.** The crossing event is measurable. Its indicator is integrable under the probability product law, so Fubini applies. -/
private theorem cross_integral (c s r : ℝ) :
    ((γ).prod γ).real
      {z : (Fin n → ℝ) × (Fin n → ℝ) |
        ¬ ((‖c • WithLp.toLp 2 z.1 - s • WithLp.toLp 2 z.2‖ ≤ r) ↔
           (‖c • WithLp.toLp 2 z.1 + s • WithLp.toLp 2 z.2‖ ≤ r))} =
    ∫ W : Fin n → ℝ, ∫ V : Fin n → ℝ,
      (if ¬ ((‖c • WithLp.toLp 2 W - s • WithLp.toLp 2 V‖ ≤ r) ↔
           (‖c • WithLp.toLp 2 W + s • WithLp.toLp 2 V‖ ≤ r))
        then (1 : ℝ) else 0) ∂γ ∂γ := by
  let B : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {z | ¬ ((‖c • WithLp.toLp 2 z.1 - s • WithLp.toLp 2 z.2‖ ≤ r) ↔
           (‖c • WithLp.toLp 2 z.1 + s • WithLp.toLp 2 z.2‖ ≤ r))}
  have hminus : MeasurableSet {z : (Fin n → ℝ) × (Fin n → ℝ) |
      ‖c • WithLp.toLp 2 z.1 - s • WithLp.toLp 2 z.2‖ ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hplus : MeasurableSet {z : (Fin n → ℝ) × (Fin n → ℝ) |
      ‖c • WithLp.toLp 2 z.1 + s • WithLp.toLp 2 z.2‖ ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  have hB : MeasurableSet B := by
    convert hminus.symmDiff hplus using 1
    ext z
    simp only [B, Set.mem_setOf_eq, Set.mem_symmDiff]
    tauto
  rw [← integral_indicator_one hB]
  have hi :
      Integrable (B.indicator
        (1 : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)) ((γ).prod γ) := by
    exact (integrable_const (1 : ℝ)).indicator hB
  simpa only [Set.indicator_apply, B, Set.mem_setOf_eq, Pi.one_apply] using
    integral_prod
      (B.indicator (1 : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)) hi

/-- Integrating a function of symmetric endpoint norms can be reduced to one radial integral and one Gaussian integral.

**Proof sketch.** Gaussian isometry invariance makes the inner integral radial. Apply the chi radial integration formula to the outer integral. -/
private theorem double_radial (hn : 0 < n) (c s : ℝ) (e₀ : E)
    (he₀ : ‖e₀‖ = 1) (F : ℝ → ℝ → ℝ) :
    (∫ W : Fin n → ℝ, ∫ V : Fin n → ℝ,
      F ‖c • WithLp.toLp 2 W + s • WithLp.toLp 2 V‖
        ‖c • WithLp.toLp 2 W - s • WithLp.toLp 2 V‖ ∂γ ∂γ) =
    ((2 : ℝ) ^ (1 - (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
      ∫ R in Set.Ioi (0 : ℝ), R ^ (n - 1) * Real.exp (-R ^ 2 / 2) *
        (∫ V : Fin n → ℝ,
          F ‖c • (R • e₀) + s • WithLp.toLp 2 V‖
            ‖c • (R • e₀) - s • WithLp.toLp 2 V‖ ∂γ) := by
  calc
    _ = ∫ W : Fin n → ℝ, ∫ V : Fin n → ℝ,
          F ‖c • (‖(WithLp.toLp 2 W : E)‖ • e₀) +
              s • WithLp.toLp 2 V‖
            ‖c • (‖(WithLp.toLp 2 W : E)‖ • e₀) -
              s • WithLp.toLp 2 V‖ ∂γ ∂γ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun W =>
        radial_integral_coordinates c s (WithLp.toLp 2 W) e₀ he₀ F)
    _ = _ := integral_gaussianPi_radial hn (fun R : ℝ =>
      ∫ V : Fin n → ℝ,
        F ‖c • (R • e₀) + s • WithLp.toLp 2 V‖
          ‖c • (R • e₀) - s • WithLp.toLp 2 V‖ ∂γ)

/-- The two squared endpoint norms admit a square completion along the chosen unit direction. -/
private theorem square_completion (c s R : ℝ) (e V : E) (he : ‖e‖ = 1) :
    ‖c • (R • e) - s • V‖ ^ 2 =
      (c * R - s * (inner ℝ e V)) ^ 2 +
        s ^ 2 * (‖V‖ ^ 2 - (inner ℝ e V) ^ 2) ∧
    ‖c • (R • e) + s • V‖ ^ 2 =
      (c * R + s * (inner ℝ e V)) ^ 2 +
        s ^ 2 * (‖V‖ ^ 2 - (inner ℝ e V) ^ 2) := by
  constructor
  · rw [norm_sub_sq_real]
    simp only [norm_smul, he, mul_one, real_inner_smul_left,
      real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  · rw [norm_add_sq_real]
    simp only [norm_smul, he, mul_one, real_inner_smul_left,
      real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    ring

/-- A polynomial Gaussian radial weight times a measurable event admits an exchange of radial and Gaussian integrals. -/
private theorem weighted_indicator_swap (k : ℕ)
    (B : Set (ℝ × (Fin n → ℝ))) (hB : MeasurableSet B) :
    (∫ R in Set.Ioi (0 : ℝ), ∫ V : Fin n → ℝ,
      B.indicator (fun z => z.1^k * Real.exp (-z.1^2/2)) (R,V) ∂γ) =
    ∫ V : Fin n → ℝ, (∫ R in Set.Ioi (0 : ℝ),
      B.indicator (fun z => z.1^k * Real.exp (-z.1^2/2)) (R,V)) ∂γ := by
  have hi : Integrable
      (B.indicator (fun z => z.1^k * Real.exp (-z.1^2/2)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (γ)) :=
    ((integrable_radial_gaussian_weight k).restrict.comp_fst (γ)).indicator hB
  exact integral_integral_swap
    (f := fun R V => B.indicator (fun z => z.1^k * Real.exp (-z.1^2/2)) (R,V)) hi

/-- The weighted radial section integral of a measurable event is measurable in the Gaussian vector. -/
private theorem weighted_indicator_measurable (k : ℕ)
    (B : Set (ℝ × (Fin n → ℝ))) (hB : MeasurableSet B) :
    Measurable (fun V : Fin n → ℝ => ∫ R in Set.Ioi (0 : ℝ),
      B.indicator (fun z => z.1^k * Real.exp (-z.1^2/2)) (R,V)) := by
  have hw : StronglyMeasurable
      (fun z : ℝ × (Fin n → ℝ) => z.1^k * Real.exp (-z.1^2/2)) := by
    fun_prop
  exact (hw.indicator hB).integral_prod_left'.measurable

/-- The scalar quadratic crossing event is measurable. -/
private theorem scalar_event_measurable (j : Fin n) (c s r : ℝ) :
    MeasurableSet {z : ℝ × (Fin n → ℝ) |
      ¬ ((c^2*z.1^2 + s^2*‖(WithLp.toLp 2 z.2 : E)‖^2 -
          2*c*s*z.1*z.2 j ≤ r^2) ↔
         (c^2*z.1^2 + s^2*‖(WithLp.toLp 2 z.2 : E)‖^2 +
          2*c*s*z.1*z.2 j ≤ r^2))} := by
  have hm : MeasurableSet {z : ℝ × (Fin n → ℝ) |
      c^2*z.1^2 + s^2*‖(WithLp.toLp 2 z.2 : E)‖^2 -
        2*c*s*z.1*z.2 j ≤ r^2} := measurableSet_le (by fun_prop) measurable_const
  have hp : MeasurableSet {z : ℝ × (Fin n → ℝ) |
      c^2*z.1^2 + s^2*‖(WithLp.toLp 2 z.2 : E)‖^2 +
        2*c*s*z.1*z.2 j ≤ r^2} := measurableSet_le (by fun_prop) measurable_const
  convert hm.symmDiff hp using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_symmDiff]
  tauto

/-- The radial integral of the quadratic ball crossing event is measurable in the Gaussian vector. -/
theorem scalar_q_measurable (k : ℕ) (j : Fin n) (c s r : ℝ) :
    Measurable (fun V : Fin n → ℝ => ∫ R in Set.Ioi (0 : ℝ),
      R^k * Real.exp (-R^2/2) *
        (if ¬ ((c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 -
          2*c*s*R*V j ≤ r^2) ↔
         (c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 +
          2*c*s*R*V j ≤ r^2)) then (1 : ℝ) else 0)) := by
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero] using
    weighted_indicator_measurable k _ (scalar_event_measurable j c s r)

/-- The polynomial Gaussian weighted crossing integral admits an exchange of radial and Gaussian integration. -/
private theorem scalar_swap (k : ℕ) (j : Fin n) (c s r : ℝ) :
    (∫ R in Set.Ioi (0 : ℝ), R^k * Real.exp (-R^2/2) *
      (∫ V : Fin n → ℝ,
        (if ¬ ((c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 -
          2*c*s*R*V j ≤ r^2) ↔
         (c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 +
          2*c*s*R*V j ≤ r^2)) then (1 : ℝ) else 0) ∂γ)) =
    ∫ V : Fin n → ℝ, (∫ R in Set.Ioi (0 : ℝ),
      R^k * Real.exp (-R^2/2) *
        (if ¬ ((c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 -
          2*c*s*R*V j ≤ r^2) ↔
         (c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 +
          2*c*s*R*V j ≤ r^2)) then (1 : ℝ) else 0)) ∂γ := by
  simp_rw [← integral_const_mul]
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero] using
    weighted_indicator_swap k _ (scalar_event_measurable j c s r)

/-- The endpoint ball-membership tests equal the scalar quadratic tests in a coordinate unit direction.

**Proof sketch.** Expand both squared Euclidean norms and use the nonnegative radius to square the two inequalities. -/
private theorem norm_scalar (j : Fin n) (c s R r : ℝ) (hr : 0 ≤ r)
    (V : Fin n → ℝ) :
    (‖c • (R • EuclideanSpace.single j (1 : ℝ)) - s • WithLp.toLp 2 V‖ ≤ r ↔
      c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 - 2*c*s*R*V j ≤ r^2) ∧
    (‖c • (R • EuclideanSpace.single j (1 : ℝ)) + s • WithLp.toLp 2 V‖ ≤ r ↔
      c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 + 2*c*s*R*V j ≤ r^2) := by
  have he : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
  have hs := square_completion c s R (EuclideanSpace.single j (1 : ℝ))
    (WithLp.toLp 2 V) he
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at hs
  have hm : ‖c • (R • EuclideanSpace.single j (1 : ℝ)) - s • WithLp.toLp 2 V‖^2 =
      c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 - 2*c*s*R*V j := by
    rw [hs.1]
    ring
  have hp : ‖c • (R • EuclideanSpace.single j (1 : ℝ)) + s • WithLp.toLp 2 V‖^2 =
      c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 + 2*c*s*R*V j := by
    rw [hs.2]
    ring
  constructor
  · rw [← hm]
    exact (sq_le_sq₀ (norm_nonneg _) hr).symm
  · rw [← hp]
    exact (sq_le_sq₀ (norm_nonneg _) hr).symm

/-- The symmetric ball crossing probability is the chi normalization times the Gaussian average of its weighted scalar radial crossing integral.

**Proof sketch.** Use Fubini to condition on a vector, apply radial Gaussian integration, expand the endpoint norms, and exchange the radial and Gaussian integrals. -/
private theorem ball_cross_radial (hn : 0 < n) (j : Fin n) (c s r : ℝ) (hr : 0 ≤ r)
    (q : (Fin n → ℝ) → ℝ)
    (hq : ∀ V, q V = ∫ R in Set.Ioi (0 : ℝ),
      R^(n-1) * Real.exp (-R^2/2) *
        (if ¬ ((c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 -
          2*c*s*R*V j ≤ r^2) ↔
         (c^2*R^2 + s^2*‖(WithLp.toLp 2 V : E)‖^2 +
          2*c*s*R*V j ≤ r^2)) then (1 : ℝ) else 0)) :
    ((γ).prod γ).real
      {z : (Fin n → ℝ) × (Fin n → ℝ) |
        ¬ ((‖c • WithLp.toLp 2 z.1 - s • WithLp.toLp 2 z.2‖ ≤ r) ↔
           (‖c • WithLp.toLp 2 z.1 + s • WithLp.toLp 2 z.2‖ ≤ r))} =
    ((2 : ℝ) ^ (1 - (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
      ∫ V : Fin n → ℝ, q V ∂γ := by
  rw [cross_integral]
  have he : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
  rw [double_radial hn c s (EuclideanSpace.single j (1 : ℝ)) he
    (fun a b => if ¬ ((b ≤ r) ↔ (a ≤ r)) then (1 : ℝ) else 0)]
  apply congrArg (fun x : ℝ =>
    ((2 : ℝ) ^ (1 - (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) * x)
  simp_rw [hq]
  rw [← scalar_swap (n-1) j c s r]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun R => by
    apply congrArg (fun x : ℝ => R^(n-1)*Real.exp (-R^2/2)*x)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun V => by
      dsimp only
      simp only [(norm_scalar j c s R r hr V).1,
        (norm_scalar j c s R r hr V).2]))

/-- A centered ball rotation sensitivity equals the chi normalization times the averaged scalar radial crossing integral. [OD14, Example 11.50; Exercise 11.17]

**Proof sketch.** Gaussian rotation invariance gives symmetric half-angle endpoints. Radial integration then gives the scalar crossing representation. -/
theorem ball_sensitivity_radial (hn : 0 < n) (j : Fin n) (r t : ℝ) (hr : 0 ≤ r)
    (q : (Fin n → ℝ) → ℝ)
    (hq : ∀ V, q V = ∫ R in Set.Ioi (0 : ℝ),
      R^(n-1) * Real.exp (-R^2/2) *
        (if ¬ (((Real.cos (t/2))^2*R^2 +
          (Real.sin (t/2))^2*‖(WithLp.toLp 2 V : E)‖^2 -
          2*Real.cos (t/2)*Real.sin (t/2)*R*V j ≤ r^2) ↔
         ((Real.cos (t/2))^2*R^2 +
          (Real.sin (t/2))^2*‖(WithLp.toLp 2 V : E)‖^2 +
          2*Real.cos (t/2)*Real.sin (t/2)*R*V j ≤ r^2)) then (1 : ℝ) else 0)) :
    rotationSensitivity {x : Fin n → ℝ | ‖(WithLp.toLp 2 x : E)‖ ≤ r} t =
    ((2 : ℝ) ^ (1 - (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
      ∫ V : Fin n → ℝ, q V ∂γ := (by
  have hA : MeasurableSet {x : Fin n → ℝ | ‖(WithLp.toLp 2 x : E)‖ ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [half_angle _ hA t]
  change ((γ).prod γ).real
      {z : (Fin n → ℝ) × (Fin n → ℝ) |
        ¬ ((‖Real.cos (t/2) • WithLp.toLp 2 z.1 -
              Real.sin (t/2) • WithLp.toLp 2 z.2‖ ≤ r) ↔
           (‖Real.cos (t/2) • WithLp.toLp 2 z.1 +
              Real.sin (t/2) • WithLp.toLp 2 z.2‖ ≤ r))} = _
  exact ball_cross_radial hn j (Real.cos (t/2)) (Real.sin (t/2)) r hr q hq
)

end BooleanAnalysis.GaussianSpace.BallCrossings
