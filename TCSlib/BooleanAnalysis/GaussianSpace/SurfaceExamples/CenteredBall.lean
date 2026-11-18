/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceArea
import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceExamples.BallCrossings
import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceExamples.RadialCrossings

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact Gaussian surface area of centered balls

## Main definitions

Balls are expressed using the Euclidean norm on the existing vector carrier.

## Main results

* `surfaceArea_centered_ball_formula`: Gaussian surface area is the chi density.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Example 11.50 and Exercise 11.17.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- Conditional radial limits and an absolute Gaussian coordinate bound give
the centered-ball surface-area formula.

**Proof sketch.** Apply dominated convergence using the integrable absolute
Gaussian coordinate. Its first moment is twice the Gaussian density at zero,
which cancels the surface-area normalization. Uniqueness of the rotation limit
identifies the Gaussian surface area. -/
private lemma surfaceArea_ball_of_radial_limits {n:ℕ} (_hn:0<n) (r:ℝ) (_hr:0<r)
 (q : ℝ → (Fin n → ℝ) → ℝ) (j:Fin n) (M:ℝ)
 (hmeas:∀t,0<t→t<1→AEStronglyMeasurable (fun v => q t v / t)
   (Measure.pi fun _ : Fin n => standardGaussianMeasure))
 (hbound:∀t,0<t→t<1→∀v,|q t v / t|≤2*M*|v j|)
 (hlim:∀v,Tendsto (fun t => q t v / t) (𝓝[>] (0:ℝ))
   (𝓝 (r^(n-1)*Real.exp (-r^2/2)*|v j|)))
 (hrepr:∀t, rotationSensitivity
   {x:Fin n→ℝ|‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖≤r} t =
   ((2:ℝ)^(1-(n:ℝ)/2)/Real.Gamma ((n:ℝ)/2))*
   ∫v,q t v ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) :
 gaussianSurfaceArea {x:Fin n→ℝ|‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖≤r} =
 ENNReal.ofReal ((2:ℝ)^(1-(n:ℝ)/2)/Real.Gamma ((n:ℝ)/2)*
 r^(n-1)*Real.exp (-r^2/2)) := by
 have hv : Integrable (fun v:Fin n→ℝ => |v j|)
     (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
   simp_rw [standardGaussianMeasure_eq]
   exact ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j).integrable_comp_of_integrable
       ((memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable le_rfl)).abs
 have h := tendsto_integral_filter_of_dominated_convergence
   (fun v => 2*M*|v j|)
   (by filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with t ht
       exact hmeas t ht.1 ht.2)
   (by filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with t ht
       exact Eventually.of_forall fun v => by
         simpa only [Real.norm_eq_abs] using hbound t ht.1 ht.2 v)
   (hv.const_mul (2*M)) (Eventually.of_forall hlim)
 have hm : (∫v:Fin n→ℝ, |v j|
     ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
     2*standardGaussianPDF 0 := by
   simpa [Pi.single_apply, ite_mul] using integral_abs_gaussianProjection (Pi.single j 1)
 simp only [integral_const_mul, hm] at h
 have hs := h.const_mul (Real.sqrt (Real.pi/2) *
   ((2:ℝ)^(1-(n:ℝ)/2)/Real.Gamma ((n:ℝ)/2)))
 have he : Real.sqrt (Real.pi / 2) *
     ((2:ℝ)^(1-(n:ℝ)/2)/Real.Gamma ((n:ℝ)/2)) *
     (r^(n-1)*Real.exp (-r^2/2)*(2*standardGaussianPDF 0)) =
     (2:ℝ)^(1-(n:ℝ)/2)/Real.Gamma ((n:ℝ)/2)*r^(n-1)*Real.exp (-r^2/2) := by
   calc
     _ = ((2:ℝ)^(1-(n:ℝ)/2)/Real.Gamma ((n:ℝ)/2)*r^(n-1)*Real.exp (-r^2/2)) *
       (Real.sqrt (Real.pi/2)*(2*standardGaussianPDF 0)) := by ring
     _ = _ := by rw [gaussian_surface_normalization,mul_one]
 rw [he] at hs
 have hball : MeasurableSet {x:Fin n→ℝ|
   ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖≤r} :=
   measurableSet_le (by fun_prop) measurable_const
 apply tendsto_nhds_unique (surfaceArea_rotation_limit hball)
 apply (ENNReal.continuous_ofReal.tendsto _).comp
 convert hs using 1
 funext t
 rw [hrepr t, integral_div]
 ring

/-- A centered ball has Gaussian surface area equal to the chi density at its
radius. [OD14, Example 11.50; Exercise 11.17]

**Proof sketch.** Rotate the Gaussian pair by half the angle to make the two
endpoints symmetric. Gaussian isometry invariance reduces the crossing
probability to radial integration. Each conditional radial crossing interval
has limiting width equal to the absolute directional Gaussian coordinate.
The bounded chi weight supplies an integrable uniform bound, so dominated
convergence applies. The first absolute Gaussian moment cancels the
rotation-to-surface-area normalization. -/
theorem surfaceArea_centered_ball_formula {n : ℕ} (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    gaussianSurfaceArea {x : Fin n → ℝ |
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ≤ r} =
      ENNReal.ofReal ((2 : ℝ) ^ (1 - (n : ℝ) / 2) /
        Real.Gamma ((n : ℝ) / 2) * r^(n-1) * Real.exp (-r^2/2)) := (by
  let j : Fin n := ⟨0, hn⟩
  let f : ℝ → ℝ := fun R => R^(n-1) * Real.exp (-R^2/2)
  let q : ℝ → (Fin n → ℝ) → ℝ := fun t V =>
    ∫ R in Set.Ioi (0 : ℝ), f R *
      (if ¬ ((Real.cos (t/2)^2*R^2 +
          Real.sin (t/2)^2*‖(WithLp.toLp 2 V : EuclideanSpace ℝ (Fin n))‖^2 -
          2*Real.cos (t/2)*Real.sin (t/2)*R*V j ≤ r^2) ↔
        (Real.cos (t/2)^2*R^2 +
          Real.sin (t/2)^2*‖(WithLp.toLp 2 V : EuclideanSpace ℝ (Fin n))‖^2 +
          2*Real.cos (t/2)*Real.sin (t/2)*R*V j ≤ r^2))
        then (1 : ℝ) else 0)
  have hq : ∀ t V, q t V =
      ∫ R in Set.Ioi (0 : ℝ),
        if ¬ ((Real.cos (t/2)^2*R^2 +
          Real.sin (t/2)^2*‖(WithLp.toLp 2 V : EuclideanSpace ℝ (Fin n))‖^2 +
          2*Real.cos (t/2)*Real.sin (t/2)*R*V j ≤ r^2) ↔
        (Real.cos (t/2)^2*R^2 +
          Real.sin (t/2)^2*‖(WithLp.toLp 2 V : EuclideanSpace ℝ (Fin n))‖^2 -
          2*Real.cos (t/2)*Real.sin (t/2)*R*V j ≤ r^2))
        then f R else 0 := by
    intro t V
    simp only [q, mul_ite, mul_one, mul_zero, iff_comm]
  obtain ⟨M, hM, hMb⟩ := radial_gaussian_weight_bounded (n-1)
  apply surfaceArea_ball_of_radial_limits hn r hr q j M
  · intro t ht ht1
    have hm := (BallCrossings.scalar_q_measurable (n-1) j
      (Real.cos (t/2)) (Real.sin (t/2)) r).div_const t
    exact hm.aestronglyMeasurable
  · intro t ht ht1 V
    rw [hq]
    exact RadialCrossings.radial_disagreement_bound ht ht1 hM
      (fun R hR => hMb R hR.le)
  · intro V
    simp_rw [hq]
    exact RadialCrossings.scalar_disagreement_limit hr
      ((by fun_prop : Continuous f).continuousOn)
  · intro t
    exact BallCrossings.ball_sensitivity_radial hn j r t hr.le (q t) (fun V => rfl)
)

end BooleanAnalysis.GaussianSpace
