/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Integration and linear geometry for localization

## Main definitions

No new definitions.

## Main results

* `continuousAt_integral_halfspace_of_boundary_null`: continuity of a
  half-space integral at parameters whose boundary has measure zero.

* `measure_inner_eq_zero_of_pair_ne_zero`: Haar-nullity of nontrivial hyperplanes.
* `continuousOn_integral_halfspace`: continuity at every nonzero cut parameter.
* `integral_halfspace_neg_eq_sub`: opposite cuts integrate to complementary totals.
* `exists_injective_complex_continuousLinearMap`: a plane of normals in dimension at least two.
* `exists_isCompact_convex_pos_integrals`: truncate two positive integrals to a common compact convex set.

## References

* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, pp.379–381.

* Mathlib, `Mathlib.MeasureTheory.Integral.Bochner.Basic`:
  dominated continuity of parameterized integrals.
* Mathlib, `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`:
  Haar-nullity of proper affine subspaces.
* Mathlib, `Mathlib.LinearAlgebra.Dimension.Finite` and
  `Mathlib.LinearAlgebra.Complex.FiniteDimensional`: finite independent families
  and real coordinates for the complex plane.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- The integral of an integrable real-valued function over a closed
half-space depends continuously on its normal and threshold at any
parameter whose boundary hyperplane has measure zero.

This is technical dominated-convergence glue for simultaneous bisection.
The normal may be zero when the boundary-null hypothesis holds; in
particular, a zero normal and nonzero threshold have empty boundary.

**Proof sketch.** Express each half-space integral using an indicator.
Outside the null boundary at the limiting parameter, the defining strict
inequality has locally constant truth value, so the indicator integrand
is continuous in the parameters. Its absolute value is bounded by the
integrable function `|f|`. Apply dominated continuity of parameterized
integrals. -/
theorem continuousAt_integral_halfspace_of_boundary_null
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (f : E → ℝ) (hf : Integrable f μ)
    (v : E) (t : ℝ)
    (hboundary : μ {x : E | inner ℝ v x = t} = 0) :
    ContinuousAt
      (fun z : E × ℝ =>
        ∫ x in {x : E | inner ℝ z.1 x ≤ z.2}, f x ∂μ)
      (v, t) :=
  (by
  let F : (E × ℝ) → E → ℝ := fun z =>
    {x : E | inner ℝ z.1 x ≤ z.2}.indicator f
  have hmeas (z : E × ℝ) : MeasurableSet {x : E | inner ℝ z.1 x ≤ z.2} :=
    measurableSet_le (by fun_prop) measurable_const
  have hcont : ∀ᵐ x ∂μ, ContinuousAt (fun z => F z x) (v, t) := by
    have hne : ∀ᵐ x ∂μ, inner ℝ v x ≠ t := by
      apply ae_iff.mpr
      simpa only [not_not] using hboundary
    filter_upwards [hne] with x hx
    have hi : ContinuousAt (fun z : E × ℝ => inner ℝ z.1 x) (v, t) :=
      (continuous_fst.inner continuous_const).continuousAt
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · apply (continuousAt_const :
        ContinuousAt (fun _ : E × ℝ => f x) (v, t)).congr_of_eventuallyEq
      filter_upwards [hi.eventually_lt continuous_snd.continuousAt hlt] with z hz
      exact indicator_of_mem
        (show x ∈ {x : E | inner ℝ z.1 x ≤ z.2} from hz.le) f
    · apply (continuousAt_const :
        ContinuousAt (fun _ : E × ℝ => (0 : ℝ)) (v, t)).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.eventually_lt hi hgt] with z hz
      exact indicator_of_notMem
        (show x ∉ {x : E | inner ℝ z.1 x ≤ z.2} from not_le_of_gt hz) f
  have hdom : ContinuousAt (fun z => ∫ x, F z x ∂μ) (v, t) :=
    continuousAt_of_dominated
      (Filter.Eventually.of_forall (fun z =>
        hf.aestronglyMeasurable.indicator (hmeas z)))
      (Filter.Eventually.of_forall (fun z =>
        Filter.Eventually.of_forall (fun x => norm_indicator_le_norm_self f x)))
      hf.norm hcont
  simpa only [F, integral_indicator (hmeas _)] using hdom
)


/-- An affine hyperplane defined by a normal and threshold that are not
both zero has Haar measure zero in a finite-dimensional real inner
product space.

This includes a zero normal with nonzero threshold, when the set is empty.

**Proof sketch.** If the normal is zero, the nonzero threshold makes the
set empty. Otherwise its defining equation describes an affine subspace.
This subspace is proper: an equation holding for every point would,
by evaluation at zero and at the normal itself, force both the threshold
and the normal to vanish. Apply Haar-nullity of proper affine subspaces. -/
theorem measure_inner_eq_zero_of_pair_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (v : E) (t : ℝ) (hvt : (v, t) ≠ (0, 0)) :
    μ {x : E | inner ℝ v x = t} = 0 :=
  (by
  by_cases hv : v = 0
  · have ht : t ≠ 0 := by
      intro ht
      exact hvt (Prod.ext hv ht)
    simp [hv, Ne.symm ht]
  · let S : AffineSubspace ℝ E :=
      { carrier := {x : E | inner ℝ v x = t}
        smul_vsub_vadd_mem := by
          intro c x y z hx hy hz
          change inner ℝ v (c • (x - y) + z) = t
          change inner ℝ v x = t at hx
          change inner ℝ v y = t at hy
          change inner ℝ v z = t at hz
          rw [inner_add_right, inner_smul_right, inner_sub_right, hx, hy, hz]
          ring }
    have hS : S ≠ ⊤ := by
      intro htop
      have hzero : (0 : E) ∈ S := by
        rw [htop]
        exact AffineSubspace.mem_top ℝ E _
      have hv_mem : v ∈ S := by
        rw [htop]
        exact AffineSubspace.mem_top ℝ E _
      change inner ℝ v 0 = t at hzero
      rw [inner_zero_right] at hzero
      change inner ℝ v v = t at hv_mem
      exact hv (inner_self_eq_zero.mp (hv_mem.trans hzero.symm))
    exact Measure.addHaar_affineSubspace μ S hS
)


/-- For an integrable real-valued function on a finite-dimensional real
inner product space with Haar measure, its closed-half-space integral
depends continuously on the normal and threshold wherever they are not
both zero.

This includes the zero-normal parameters with nonzero threshold needed
when cuts are parametrized by a sphere.

**Proof sketch.** At each nonzero parameter pair, the boundary hyperplane
has Haar measure zero. Apply continuity of half-space integrals at
boundary-null parameters, then restrict that continuity to the punctured
parameter space. -/
theorem continuousOn_integral_halfspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → ℝ) (hf : Integrable f μ) :
    ContinuousOn
      (fun z : E × ℝ =>
        ∫ x in {x : E | inner ℝ z.1 x ≤ z.2}, f x ∂μ)
      {z : E × ℝ | z ≠ (0, 0)} :=
  (by
  intro z hz
  exact (continuousAt_integral_halfspace_of_boundary_null μ f hf z.1 z.2
    (measure_inner_eq_zero_of_pair_ne_zero μ z.1 z.2 hz)).continuousWithinAt
)

/-- Negating a half-space's normal and threshold replaces its integral
by the total integral minus the original half-space integral, provided
the boundary has measure zero.

**Proof sketch.** The opposite closed half-space agrees almost everywhere
with the complement of the original half-space: their discrepancy is
contained in the null boundary. Replace the integration set by that
complement and apply the complementary-set integral identity. -/
theorem integral_halfspace_neg_eq_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (f : E → ℝ) (hf : Integrable f μ)
    (v : E) (t : ℝ)
    (hboundary : μ {x : E | inner ℝ v x = t} = 0) :
    (∫ x in {x : E | inner ℝ (-v) x ≤ -t}, f x ∂μ) =
      (∫ x, f x ∂μ) -
        ∫ x in {x : E | inner ℝ v x ≤ t}, f x ∂μ :=
  (by
  have hne : ∀ᵐ x ∂μ, inner ℝ v x ≠ t := by
    apply ae_iff.mpr
    simpa only [not_not] using hboundary
  calc
    _ = ∫ x in {x : E | inner ℝ v x ≤ t}ᶜ, f x ∂μ := by
      apply setIntegral_congr_set
      filter_upwards [hne] with x hx
      change (inner ℝ (-v) x ≤ -t) = (¬ inner ℝ v x ≤ t)
      rw [inner_neg_left]
      apply propext
      constructor
      · intro h hle
        apply hx
        linarith
      · intro h
        have := lt_of_not_ge h
        linarith
    _ = _ := setIntegral_compl (measurableSet_le (by fun_prop) measurable_const) hf
)

/-- A real normed vector space with real finrank at least two admits an
injective continuous real-linear map from the complex plane.

This is technical linear-algebra glue for choosing a plane of cut normals.

**Proof sketch.** Choose two linearly independent vectors. Express complex
numbers in the real basis consisting of one and the imaginary unit, and
send their coordinates to the corresponding linear combination of the
chosen vectors. Linear independence gives injectivity. The resulting
linear map is continuous because its domain is finite-dimensional. -/
theorem exists_injective_complex_continuousLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ J : ℂ →L[ℝ] E, Function.Injective J :=
  (by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  let e : ℂ ≃ₗ[ℝ] Submodule.span ℝ (Set.range v) :=
    Complex.basisOneI.repr.trans hv.linearCombinationEquiv
  let J : ℂ →ₗ[ℝ] E := (Submodule.span ℝ (Set.range v)).subtype.comp e.toLinearMap
  refine ⟨⟨J, J.continuous_of_finiteDimensional⟩, ?_⟩
  exact Subtype.val_injective.comp e.injective
)

/-- Two real functions with positive full integrals under an arbitrary
measure on a proper real normed space have positive integrals on one
common compact convex set.

This is technical truncation glue for passing from full-space tests to
the compact-body localization argument in [LS93, Lemma 2.5], not a
separately numbered result there. No continuity or separate integrability
hypothesis is needed: each positive Bochner integral forces integrability.

**Proof sketch.** The positive full integrals imply integrability of both
functions. Closed balls about zero with natural radii form a measurable
increasing exhaustion of the space. The existing convergence theorem for
integrals over increasing measurable sets makes both restricted integrals
converge to their positive full integrals. Eventually both are positive;
choose one common ball. Properness makes that ball compact, and every
closed ball in a real normed space is convex. -/
theorem exists_isCompact_convex_pos_integrals
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (F G : E → ℝ)
    (hF : 0 < ∫ x, F x ∂μ) (hG : 0 < ∫ x, G x ∂μ) :
    ∃ K : Set E, IsCompact K ∧ Convex ℝ K ∧
      (0 < ∫ x in K, F x ∂μ) ∧ (0 < ∫ x in K, G x ∂μ) :=
  (by
  let s (n : ℕ) := Metric.closedBall (0 : E) (n : ℝ)
  have hs : Monotone s := fun i j hij => Metric.closedBall_subset_closedBall (by exact_mod_cast hij)
  have hunion : (⋃ n : ℕ, s n) = Set.univ := Metric.iUnion_closedBall_nat 0
  have hpos (T : E → ℝ) (hT : 0 < ∫ x, T x ∂μ) :
      ∀ᶠ n in Filter.atTop, 0 < ∫ x in s n, T x ∂μ := by
    have hi : Integrable T μ := Integrable.of_integral_ne_zero (ne_of_gt hT)
    have hc := tendsto_setIntegral_of_monotone (fun n => measurableSet_closedBall) hs
      (show IntegrableOn T (⋃ n : ℕ, s n) μ from by
        rw [hunion]
        exact hi.integrableOn)
    rw [hunion, setIntegral_univ] at hc
    exact hc (Ioi_mem_nhds hT)
  obtain ⟨n, hnF, hnG⟩ := ((hpos F hF).and (hpos G hG)).exists
  exact ⟨s n, isCompact_closedBall _ _, convex_closedBall _ _, hnF, hnG⟩
)


end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
