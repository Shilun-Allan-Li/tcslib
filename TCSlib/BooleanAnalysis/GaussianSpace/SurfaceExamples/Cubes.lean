/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceArea
import TCSlib.BooleanAnalysis.GaussianSpace.Borell.Indicator
import Mathlib.Algebra.Ring.GeomSum

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian surface area of coordinate cubes

## Main definitions

Coordinate cubes are expressed directly as intersections of coordinate halfspaces.

## Main results

* `surfaceArea_coordinate_cube`: the surface-area formula `n φ(t) Φ(t)^(n-1)`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.3 and §11.4, Example 11.50.
* [KOS08] A. Klivans, R. O'Donnell and R. Servedio, Learning geometric concepts
  via Gaussian surface area, FOCS (2008), 541–550.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions

/-- The Gaussian measure of an upper coordinate cube is the product of its
one-dimensional marginal probabilities. -/
private lemma cube_volume (n : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin n => standardGaussianMeasure).real
      {x : Fin n → ℝ | ∀ i, x i ≤ t} =
      (standardGaussianMeasure.real (Set.Iic t)) ^ n := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    rw [standardGaussianMeasure_eq]
    infer_instance
  have hset : {x : Fin n → ℝ | ∀ i, x i ≤ t} =
      Set.pi Set.univ (fun _ : Fin n => Set.Iic t) := by
    ext x
    change (∀ i, x i ≤ t) ↔ ∀ i ∈ Set.univ, x i ≤ t
    simp only [Set.mem_univ, forall_true_left]
  rw [hset, measureReal_def, Measure.pi_pi]
  simp [measureReal_def, ENNReal.toReal_pow]
/-- Indicator stability of an upper coordinate cube is a power of the scalar
joint-membership probability. [OD14, §11.3, Def. 11.18]

**Proof sketch.** Write stability as joint Gaussian membership. Identify a pair
of Gaussian vectors with a vector of independent pairs; joint cube membership
is then a product event, so its probability factors over coordinates. -/
private lemma cube_stability_product (n : ℕ) (t ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    gaussianNoiseStability ρ
      (({x : Fin n → ℝ | ∀ i, x i ≤ t} : Set (Fin n → ℝ)).indicator (fun _ => (1 : ℝ))) =
    ((standardGaussianMeasure.prod standardGaussianMeasure).real
      {z : ℝ × ℝ | z.1 ≤ t ∧ ρ * z.1 + Real.sqrt (1 - ρ^2) * z.2 ≤ t}) ^ n := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by rw [standardGaussianMeasure_eq]; infer_instance
  let A : Set (Fin n → ℝ) := {x | ∀ i, x i ≤ t}
  let μ := (Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
    (Measure.pi fun _ : Fin n => standardGaussianMeasure)
  let q : ((Fin n → ℝ) × (Fin n → ℝ)) → ((Fin n → ℝ) × (Fin n → ℝ)) :=
    fun z => (z.1, fun i => ρ * z.1 i + Real.sqrt (1 - ρ^2) * z.2 i)
  let D := q ⁻¹' (A ×ˢ A)
  let S : Set (ℝ × ℝ) := {z | z.1 ≤ t ∧ ρ * z.1 + Real.sqrt (1 - ρ^2) * z.2 ≤ t}
  have hA : MeasurableSet A := by
    change MeasurableSet {x : Fin n → ℝ | ∀ i, x i ≤ t}
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
  have hD : MeasurableSet D := (hA.prod hA).preimage (by fun_prop)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => standardGaussianMeasure) (fun _ => standardGaussianMeasure)
  have hset : e ⁻¹' D = Set.pi Set.univ (fun _ : Fin n => S) := by
    ext z
    change ((∀ i, (z i).1 ≤ t) ∧
      (∀ i, ρ * (z i).1 + Real.sqrt (1 - ρ^2) * (z i).2 ≤ t)) ↔
      (∀ i ∈ Set.univ, (z i).1 ≤ t ∧ ρ * (z i).1 + Real.sqrt (1 - ρ^2) * (z i).2 ≤ t)
    simp only [Set.mem_univ, forall_true_left, forall_and]
  have hprod : μ.real D = ((standardGaussianMeasure.prod standardGaussianMeasure).real S)^n := by
    rw [← he.measureReal_preimage hD.nullMeasurableSet]
    change ((Measure.pi fun _ : Fin n =>
      standardGaussianMeasure.prod standardGaussianMeasure) (e ⁻¹' D)).toReal = _
    rw [hset, Measure.pi_pi]
    simp [measureReal_def, ENNReal.toReal_pow]
  rw [gaussianNoiseStability_indicator_measure hρ hA,
    correlatedGaussianMeasure_eq, measureReal_def,
    Measure.map_apply (by fun_prop) (hA.prod hA)]
  exact hprod
/-- A finite geometric sum factors the change of a power. -/
private lemma pow_crossing_factor (F s c θ : ℝ) (n : ℕ) :
    c * (2*(F^n-(F-s/2)^n)) / θ =
      (c*s/θ) * ∑ i ∈ Finset.range n, F^i*(F-s/2)^(n-1-i) := by
  rw [← geom_sum₂_mul]
  ring
/-- A crossing quotient for a product of `n` equal factors gains the factor
`n F^(n-1)` in its limit.

**Proof sketch.** Factor the difference of powers by a finite geometric sum.
The scalar crossing quotient converges by assumption, while each term of the
sum converges to `F^(n-1)`. -/
private lemma pow_crossing_limit (F D c : ℝ) (n : ℕ) (s : ℝ → ℝ)
    (hs : Tendsto s (𝓝[>] (0:ℝ)) (𝓝 0))
    (hd : Tendsto (fun θ => c*s θ/θ) (𝓝[>] (0:ℝ)) (𝓝 D)) :
    Tendsto (fun θ => c*(2*(F^n-(F-s θ/2)^n))/θ)
      (𝓝[>] (0:ℝ)) (𝓝 ((n:ℝ)*F^(n-1)*D)) := by
  simp_rw [pow_crossing_factor]
  have hh : Tendsto (fun θ => ∑ i ∈ Finset.range n,
      F^i*(F-s θ/2)^(n-1-i)) (𝓝[>] (0:ℝ))
      (𝓝 ((n:ℝ)*F^(n-1))) := by
    have hu := tendsto_finset_sum (Finset.range n) (fun i hi =>
      (tendsto_const_nhds (x:=F^i)).mul
        (((tendsto_const_nhds (x:=F)).sub (hs.div_const 2)).pow (n-1-i)))
    simpa only [zero_div, sub_zero, geom_sum₂_self] using hu
  simpa only [mul_comm D] using hd.mul hh
/-- Upper coordinate cubes are measurable. -/
private lemma cube_measurable (n : ℕ) (t : ℝ) :
    MeasurableSet {x : Fin n → ℝ | ∀ i, x i ≤ t} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
/-- The sensitivity of a coordinate cube is determined by its marginal
probability and its one-dimensional sensitivity. [OD14, §11.3, Def. 11.42]

**Proof sketch.** Apply the existing sensitivity-versus-stability identity in
dimensions `n` and one, and substitute the product formulas for cube measure
and stability. -/
private lemma cube_sensitivity (n : ℕ) (t θ : ℝ) (hθ : θ ∈ Set.Icc (0:ℝ) Real.pi) :
    rotationSensitivity {x : Fin n → ℝ | ∀ i, x i ≤ t} θ =
      2*((standardGaussianMeasure.real (Set.Iic t))^n -
        (standardGaussianMeasure.real (Set.Iic t) -
          rotationSensitivity {x : Fin 1 → ℝ | ∀ i, x i ≤ t} θ / 2)^n) := by
  have hcos : Real.cos θ ∈ Set.Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hsingle := rotationSensitivity_eq_stability (cube_measurable 1 t) θ hθ
  rw [cube_volume, pow_one, cube_stability_product 1 t _ hcos, pow_one] at hsingle
  rw [rotationSensitivity_eq_stability (cube_measurable n t) θ hθ,
    cube_volume, cube_stability_product n t _ hcos]
  have h := (show (standardGaussianMeasure.prod standardGaussianMeasure).real
      {z : ℝ × ℝ | z.1 ≤ t ∧ Real.cos θ * z.1 + Real.sqrt (1-(Real.cos θ)^2)*z.2 ≤ t} =
      standardGaussianMeasure.real (Set.Iic t) -
        rotationSensitivity {x : Fin 1 → ℝ | ∀ i, x i ≤ t} θ / 2 by linarith [hsingle])
  rw [h]
/-- The standard Gaussian measure of a closed lower half-line equals its CDF. -/
private lemma gaussian_Iic_real (t : ℝ) :
    standardGaussianMeasure.real (Set.Iic t) = standardGaussianCDF t := by
  have hpdf : ProbabilityTheory.gaussianPDFReal 0 1 = standardGaussianPDF := by
    funext x
    rw [standardGaussianPDF_eq, ProbabilityTheory.gaussianPDFReal_def]
    norm_num
  rw [standardGaussianCDF_eq_integral, standardGaussianMeasure_eq, measureReal_def,
    ProbabilityTheory.gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal, hpdf]
  exact integral_nonneg fun x => (standardGaussianPDF_pos x).le
/-- The Gaussian surface area of `{x | ∀ i, x i ≤ t}` is
`n φ(t) Φ(t)^(n-1)`, including dimension zero.
[OD14, Example 11.50; KOS08]

**Proof sketch.** Independence makes cube volume and joint-membership
probabilities powers of their scalar counterparts. The difference-of-powers
factorization reduces the rotation quotient to the known halfspace quotient,
multiplied by a geometric sum tending to `n Φ(t)^(n-1)`. Apply the defining
surface-area rotation limit. -/
theorem surfaceArea_coordinate_cube (n : ℕ) (t : ℝ) :
    gaussianSurfaceArea {x : Fin n → ℝ | ∀ i, x i ≤ t} =
      ENNReal.ofReal ((n:ℝ)*standardGaussianPDF t*(standardGaussianCDF t)^(n-1)) := (by
  have hset : {x : Fin 1 → ℝ | ∀ i, x i ≤ t} =
      {x : Fin 1 → ℝ | ∑ i, (1:ℝ)*x i ≤ t} := by ext x; simp
  have hs : Tendsto (rotationSensitivity {x : Fin 1 → ℝ | ∀ i, x i ≤ t})
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
    (rotationSensitivity_tendsto_zero (cube_measurable 1 t)).mono_left nhdsWithin_le_nhds
  have hd := halfspace_rotation_quotient_tendsto (fun _ : Fin 1 => (1:ℝ)) (by simp) t
  rw [← hset] at hd
  have hp := pow_crossing_limit (standardGaussianMeasure.real (Set.Iic t))
    (standardGaussianPDF t) (Real.sqrt (Real.pi/2)) n
    (rotationSensitivity {x : Fin 1 → ℝ | ∀ i, x i ≤ t}) hs hd
  have he : ∀ᶠ θ : ℝ in 𝓝[>] (0:ℝ),
      rotationSensitivity {x : Fin n → ℝ | ∀ i, x i ≤ t} θ =
      2*((standardGaussianMeasure.real (Set.Iic t))^n -
        (standardGaussianMeasure.real (Set.Iic t) -
          rotationSensitivity {x : Fin 1 → ℝ | ∀ i, x i ≤ t} θ/2)^n) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds Real.pi_pos)] with θ hθ hθpi
    exact cube_sensitivity n t θ ⟨hθ.le, hθpi.le⟩
  have hp' : Tendsto (fun θ => Real.sqrt (Real.pi/2)*
      rotationSensitivity {x : Fin n → ℝ | ∀ i, x i ≤ t} θ/θ)
      (𝓝[>] (0:ℝ)) (𝓝 ((n:ℝ)*standardGaussianPDF t*(standardGaussianCDF t)^(n-1))) := by
    simpa only [gaussian_Iic_real, mul_assoc, mul_comm, mul_left_comm] using
      hp.congr' (he.mono (fun θ h => by rw [h]))
  exact tendsto_nhds_unique (surfaceArea_rotation_limit (cube_measurable n t))
    (ENNReal.continuous_ofReal.tendsto _ |>.comp hp')
)

end BooleanAnalysis.GaussianSpace
