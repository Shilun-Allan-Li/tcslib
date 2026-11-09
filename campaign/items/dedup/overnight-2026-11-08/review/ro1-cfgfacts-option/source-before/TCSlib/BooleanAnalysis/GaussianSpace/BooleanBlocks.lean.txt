/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov
import TCSlib.BooleanAnalysis.GaussianSpace.NormalizedSums

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Boolean Bobkov under finite coordinate reindexing

## Main definitions

The existing Boolean derivative is the false/true half difference. The array
form below writes its nested updates explicitly and introduces no second
derivative operator.

## Main results

* Currying preserves finite coordinate-product measures.
* Boolean Bobkov transports to arbitrary finite coordinate types and arrays
  under the independent uniform Boolean law.

The array form is used with normalized Boolean blocks in the Gaussian limit.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Bobkov's inequality, equation (11.15).
-/

open MeasureTheory Filter
open scoped BigOperators NNReal ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

/-- Currying preserves a finite product of coordinate measures when the index
and value types are finite and singleton sets are measurable.

**Proof sketch.** Compare singleton masses. The inverse image of an array is
its uncurried function, and both masses are the same finite product, regrouped
by the two coordinate indices. -/
lemma measurePreserving_finiteCurry {ι κ β : Type*}
    [Fintype ι] [Fintype κ] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : ι → κ → Measure β) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry ι κ β)
      (Measure.pi fun p : ι × κ => μ p.1 p.2)
      (Measure.pi fun i : ι => Measure.pi fun j : κ => μ i j) := by
  classical
  refine ⟨(MeasurableEquiv.curry ι κ β).measurable, ?_⟩
  apply Measure.ext_of_singleton
  intro x
  rw [(MeasurableEquiv.curry ι κ β).map_apply]
  have hpre : (MeasurableEquiv.curry ι κ β) ⁻¹' {x} = {Function.uncurry x} := by
    ext y
    change Function.curry y = x ↔ y = Function.uncurry x
    exact ⟨fun h => by rw [← h, Function.uncurry_curry], fun h => by
      rw [h, Function.curry_uncurry]⟩
  rw [hpre, ← Set.univ_pi_singleton, Measure.pi_pi,
    ← Set.univ_pi_singleton, Measure.pi_pi]
  simp_rw [← Set.univ_pi_singleton, Measure.pi_pi]
  exact Fintype.prod_prod_type _

/-- The Boolean Bobkov inequality holds with coordinates indexed by any finite
type, using integration under independent uniform Boolean coordinates.
[OD14, §11.4, equation (11.15)]

**Proof sketch.** Reindex the coordinates by their equivalence with Fin of the
cardinality. This preserves the uniform product law, transports false/true
updates, and reindexes the squared-gradient sum. Apply the existing cube
Bobkov inequality. -/
lemma bobkov_inequality_finite_index {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    closedGaussianProfile (∫ x : ι → Bool, f x
      ∂(Measure.pi fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)) ≤
      ∫ x : ι → Bool, Real.sqrt (closedGaussianProfile (f x) ^ 2 +
        ∑ i : ι, ((f (Function.update x i false) - f (Function.update x i true)) / 2) ^ 2)
        ∂(Measure.pi fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let r := MeasurableEquiv.piCongrLeft (fun _ : ι => Bool) e
  let g : BooleanFunc (Fintype.card ι) := fun y => f (r y)
  have hp : MeasurePreserving r
      (Measure.pi fun _ : Fin (Fintype.card ι) => (PMF.uniformOfFintype Bool).toMeasure)
      (Measure.pi fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure) :=
    measurePreserving_piCongrLeft (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure) e
  have hup (y : BoolCube (Fintype.card ι)) (j : Fin (Fintype.card ι)) (b : Bool) :
      r (Function.update y j b) = Function.update (r y) (e j) b := by
    ext i
    obtain ⟨k, rfl⟩ := e.surjective i
    by_cases h : k = j
    · subst k
      simp [r, MeasurableEquiv.piCongrLeft_apply_apply]
    · have he : e k ≠ e j := e.injective.ne h
      simp [r, MeasurableEquiv.piCongrLeft_apply_apply, h, he]
  have hgrad (y : BoolCube (Fintype.card ι)) :
      (∑ j, derivative j g y ^ 2) =
        ∑ i : ι, ((f (Function.update (r y) i false) -
          f (Function.update (r y) i true)) / 2) ^ 2 := by
    refine Fintype.sum_equiv e _ _ fun j => ?_
    simp only [derivative, g, hup]
  have hmean : expect g = ∫ x : ι → Bool, f x
      ∂(Measure.pi fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure) :=
    (integral_uniformBool_pi_eq_expect g).symm.trans (hp.integral_comp' f)
  have hfun : bobkovFunctional g =
      ∫ x : ι → Bool, Real.sqrt (closedGaussianProfile (f x) ^ 2 +
        ∑ i : ι, ((f (Function.update x i false) - f (Function.update x i true)) / 2) ^ 2)
        ∂(Measure.pi fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure) := by
    rw [bobkovFunctional, ← integral_uniformBool_pi_eq_expect]
    simp_rw [hgrad]
    simpa only [g] using hp.integral_comp' (fun x : ι → Bool =>
      Real.sqrt (closedGaussianProfile (f x) ^ 2 +
        ∑ i : ι, ((f (Function.update x i false) - f (Function.update x i true)) / 2) ^ 2))
  have h := bobkov_inequality g (fun y => hf (r y))
  rwa [hmean, hfun] at h

/-- The Boolean Bobkov inequality holds for arrays of independent uniform
Boolean coordinates, with the squared-gradient sum taken over both array
indices. [OD14, §11.4, equation (11.15)]

**Proof sketch.** Apply the finite-index inequality to the product of the two
index types. Currying preserves its law and converts a single coordinate
update into the corresponding nested array update. Regroup the finite sum. -/
lemma bobkov_inequality_array {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : (ι → κ → Bool) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    closedGaussianProfile (∫ x : ι → κ → Bool, f x
      ∂(Measure.pi fun _ : ι =>
        Measure.pi fun _ : κ => (PMF.uniformOfFintype Bool).toMeasure)) ≤
      ∫ x : ι → κ → Bool,
        Real.sqrt (closedGaussianProfile (f x) ^ 2 + ∑ i : ι, ∑ j : κ,
          ((f (Function.update x i (Function.update (x i) j false)) -
            f (Function.update x i (Function.update (x i) j true))) / 2) ^ 2)
        ∂(Measure.pi fun _ : ι =>
          Measure.pi fun _ : κ => (PMF.uniformOfFintype Bool).toMeasure) := by
  let r := MeasurableEquiv.curry ι κ Bool
  have hp := measurePreserving_finiteCurry
    (fun (_ : ι) (_ : κ) => (PMF.uniformOfFintype Bool).toMeasure)
  have h := bobkov_inequality_finite_index (fun y => f (r y)) (fun y => hf (r y))
  have hmean : (∫ y : ι × κ → Bool, f (r y)
      ∂(Measure.pi fun _ : ι × κ => (PMF.uniformOfFintype Bool).toMeasure)) =
      ∫ x : ι → κ → Bool, f x
        ∂(Measure.pi fun _ : ι =>
          Measure.pi fun _ : κ => (PMF.uniformOfFintype Bool).toMeasure) :=
    hp.integral_comp' f
  rw [hmean] at h
  convert h using 1
  symm
  calc
    (∫ y : ι × κ → Bool,
        Real.sqrt (closedGaussianProfile (f (r y)) ^ 2 + ∑ p : ι × κ,
          ((f (r (Function.update y p false)) -
            f (r (Function.update y p true))) / 2) ^ 2)
        ∂(Measure.pi fun _ : ι × κ => (PMF.uniformOfFintype Bool).toMeasure)) =
      ∫ y : ι × κ → Bool,
        Real.sqrt (closedGaussianProfile (f (r y)) ^ 2 + ∑ i : ι, ∑ j : κ,
          ((f (Function.update (r y) i (Function.update (r y i) j false)) -
            f (Function.update (r y) i (Function.update (r y i) j true))) / 2) ^ 2)
        ∂(Measure.pi fun _ : ι × κ => (PMF.uniformOfFintype Bool).toMeasure) := by
      congr 1
      funext y
      simp only [Fintype.sum_prod_type, r, MeasurableEquiv.coe_curry, Function.curry_update]
    _ = _ := by
      exact hp.integral_comp' (fun x : ι → κ → Bool =>
        Real.sqrt (closedGaussianProfile (f x) ^ 2 + ∑ i : ι, ∑ j : κ,
          ((f (Function.update x i (Function.update (x i) j false)) -
            f (Function.update x i (Function.update (x i) j true))) / 2) ^ 2))

end BooleanAnalysis.GaussianSpace
