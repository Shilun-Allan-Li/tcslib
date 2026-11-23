/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compactly supported measurable fibers

## Main definitions

No new definitions.

## Main results

* `integrable_fiber_of_measurable_bounded_hasCompactSupport`: every
  fiber of a bounded measurable compactly supported real function is
  integrable against a measure finite on compact sets.
* `hasCompactSupport_integral_fiber`: integrating the second variable preserves
  compact support.
* `bounded_integral_fiber_of_bounded_hasCompactSupport`: integrating a bounded compactly supported function
  gives a uniformly bounded marginal.

## References

* [Gar02] Richard J. Gardner, *The Brunn–Minkowski inequality*,
  Bulletin of the American Mathematical Society 39 (2002), 355–405,
  Theorem 4.2, induction by integrating fibers. These lemmas isolate
  elementary support and integrability prerequisites for the bounded
  compactly supported version of that argument.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- Every fiber of a bounded measurable compactly supported real function
is integrable against a measure finite on compact sets.
[Gar02, Theorem 4.2, fiber-integration prerequisite]

This statement applies to every parameter, rather than only almost every
parameter. No continuity of the function, measure on the parameter
space, or sigma-finiteness assumption is required.

**Proof sketch.** Project the compact topological support onto the second
factor. Each fiber vanishes outside this same compact set, which has
finite measure. Its measurability and the uniform bound give
integrability on that set; vanishing outside gives integrability on the
whole second factor. -/
theorem integrable_fiber_of_measurable_bounded_hasCompactSupport
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    {f : X × Y → ℝ} (hf : Measurable f) (hfc : HasCompactSupport f)
    (hbound : ∃ M : ℝ, ∀ p : X × Y, |f p| ≤ M) :
    ∀ x : X, Integrable (fun y : Y => f (x, y)) μ :=
  (by
  obtain ⟨M, hM⟩ := hbound
  have hK : IsCompact (Set.image Prod.snd (tsupport f)) := hfc.image continuous_snd
  intro x
  have hs : Function.support (fun y : Y => f (x, y)) ⊆ Set.image Prod.snd (tsupport f) := by
    intro y hy
    exact ⟨(x, y), subset_tsupport f hy, rfl⟩
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    (hf.comp measurable_prodMk_left).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hM (x, y))
)

/-- Integrating a compactly supported real function in its second variable
produces a compactly supported function of the first variable.
[Gar02, Theorem 4.2, fiber-integration prerequisite]

No measurability, integrability, boundedness, or finiteness assumption is
required. The integral vanishes outside the compact first projection of
the original topological support.

**Proof sketch.** Project the compact topological support onto the first
factor. Outside this projection every value of the corresponding fiber
is zero, so its integral is zero. Containment of the marginal support in
that compact set gives compact support of the marginal. -/
theorem hasCompactSupport_integral_fiber
    {X Y : Type*} [TopologicalSpace X] [R1Space X]
    [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) {f : X × Y → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (fun x : X => ∫ y : Y, f (x, y) ∂μ) :=
  (by
  apply HasCompactSupport.intro (hfc.image continuous_fst)
  intro x hx
  have hz : (fun y : Y => f (x, y)) = fun _ => 0 := by
    funext y
    by_contra h
    exact hx ⟨(x, y), subset_tsupport f h, rfl⟩
  rw [hz, integral_zero]
)

/-- The fiber integrals of a uniformly bounded compactly supported real
function are uniformly bounded when the measure is finite on compact sets.
[Gar02, Theorem 4.2, fiber-integration prerequisite]

No measurability or integrability assumption on the function is needed.

**Proof sketch.** Project the compact topological support onto the second
factor. Every fiber vanishes outside that fixed compact set. Restrict its
integral to this set and apply the standard bound by the uniform bound
times the measure of the set. This finite bound is independent of the
first parameter. -/
theorem bounded_integral_fiber_of_bounded_hasCompactSupport
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    {f : X × Y → ℝ} (hfc : HasCompactSupport f)
    (hbound : ∃ M : ℝ, ∀ p : X × Y, |f p| ≤ M) :
    ∃ M : ℝ, ∀ x : X, |∫ y : Y, f (x, y) ∂μ| ≤ M :=
  (by
  obtain ⟨M, hM⟩ := hbound
  let K := Set.image Prod.snd (tsupport f)
  have hK : IsCompact K := hfc.image continuous_snd
  letI : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  refine ⟨M * (μ.restrict K).real Set.univ, ?_⟩
  intro x
  have hzero : ∀ y, y ∉ K → f (x, y) = 0 := by
    intro y hy
    by_contra h
    exact hy ⟨(x, y), subset_tsupport f h, rfl⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := μ.restrict K) (f := fun y => f (x, y)) (C := M)
      (Filter.Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using hM (x, y))))
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
