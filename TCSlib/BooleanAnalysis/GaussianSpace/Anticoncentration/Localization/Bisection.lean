/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Basic
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Antipodal
import Mathlib.Topology.Order.IntermediateValue

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hyperplane bisection of signed integrals

## Main definitions

No new definitions.

## Main results

* `exists_hyperplane_bisect_integrals`: two integrable signed functions have
  a common bisecting hyperplane when one total is nonzero and dimension is at least two.
* `exists_pivot_hyperplane_bisect_integral`: a cut through a prescribed pivot
  bisects an integrable function, with its normal in a prescribed two-plane.
* `exists_pivot_hyperplane_bisect_integral_pos`: choose the side that preserves
  positivity of a second integral.

## References

* [Hat02] A. Hatcher, *Algebraic Topology*, Cambridge University Press,
  2002, Theorem 1.10: the two-dimensional Borsuk–Ulam theorem.
* [LS93] L. Lovász and M. Simonovits, *Random Walks in a Convex Body and an
  Improved Volume Algorithm*, Random Structures & Algorithms 4(4) (1993),
  359–412, Lemma 2.5, proof of Claim 1, p. 379.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- In a finite-dimensional real inner product space of dimension at
least two, two integrable real-valued functions have a genuine affine
hyperplane bisecting both integrals, provided the first total integral
is nonzero.

This is a signed-integral application of the two-dimensional
Borsuk–Ulam theorem [Hat02, Thm. 1.10]. Unlike the usual nonnegative-mass
formulation, the functions may be signed; the nonzero first total
excludes the degenerate zero-normal cut parameters.

**Proof sketch.** Choose an injective real-linear map from the complex
plane into the ambient space. Parametrize cuts by its image normals and
a real threshold, and encode the two integrals minus half their totals
as a complex-valued map. Half-space integral continuity makes this map
continuous away from zero. Nullity of the boundary and complementary
integration make it odd there. Apply the punctured-space odd-zero
result. The resulting normal cannot vanish: then the nonzero threshold
would make the first half-space integral either zero or its full total,
contradicting its nonzero total and bisection. -/
theorem exists_hyperplane_bisect_integrals
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (f g : E → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (htotal : (∫ x, f x ∂μ) ≠ 0) :
    ∃ (v : E) (t : ℝ), v ≠ 0 ∧
      (∫ x in {x : E | inner ℝ v x ≤ t}, f x ∂μ) =
        (∫ x, f x ∂μ) / 2 ∧
      (∫ x in {x : E | inner ℝ v x ≤ t}, g x ∂μ) =
        (∫ x, g x ∂μ) / 2 :=
  (by
  obtain ⟨J, hJ⟩ := exists_injective_complex_continuousLinearMap hdim
  let P : ℂ × ℝ → E × ℝ := fun p => (J p.1, p.2)
  have hP : Continuous P := (J.continuous.comp continuous_fst).prodMk continuous_snd
  have hPne (p : ℂ × ℝ) (hp : p ≠ 0) : P p ≠ (0, 0) := by
    intro h
    apply hp
    apply Prod.ext
    · apply hJ
      exact (congrArg Prod.fst h).trans J.map_zero.symm
    · exact congrArg (fun q : E × ℝ => q.2) h
  let A : (E → ℝ) → (E × ℝ) → ℝ :=
    fun h p => ∫ x in {x : E | inner ℝ p.1 x ≤ p.2}, h x ∂μ
  let F : ℂ × ℝ → ℂ := fun p =>
    ⟨A f (P p) - (∫ x, f x ∂μ) / 2,
      A g (P p) - (∫ x, g x ∂μ) / 2⟩
  have hcf : ContinuousOn (fun p => A f (P p)) {p : ℂ × ℝ | p ≠ 0} :=
    (continuousOn_integral_halfspace μ f hf).comp hP.continuousOn hPne
  have hcg : ContinuousOn (fun p => A g (P p)) {p : ℂ × ℝ | p ≠ 0} :=
    (continuousOn_integral_halfspace μ g hg).comp hP.continuousOn hPne
  have hF : ContinuousOn F {p : ℂ × ℝ | p ≠ 0} :=
    Complex.equivRealProdCLM.symm.continuous.comp_continuousOn
      ((hcf.sub continuousOn_const).prodMk (hcg.sub continuousOn_const))
  have hodd (p : ℂ × ℝ) (hp : p ≠ 0) : F (-p) = -F p := by
    have hb := measure_inner_eq_zero_of_pair_ne_zero μ (J p.1) p.2 (hPne p hp)
    have hff := integral_halfspace_neg_eq_sub μ f hf (J p.1) p.2 hb
    have hgg := integral_halfspace_neg_eq_sub μ g hg (J p.1) p.2 hb
    apply Complex.ext
    · change (∫ x in {x : E | inner ℝ (J (-p.1)) x ≤ -p.2}, f x ∂μ) -
          (∫ x, f x ∂μ) / 2 =
        -((∫ x in {x : E | inner ℝ (J p.1) x ≤ p.2}, f x ∂μ) -
          (∫ x, f x ∂μ) / 2)
      rw [map_neg, hff]
      ring
    · change (∫ x in {x : E | inner ℝ (J (-p.1)) x ≤ -p.2}, g x ∂μ) -
          (∫ x, g x ∂μ) / 2 =
        -((∫ x in {x : E | inner ℝ (J p.1) x ≤ p.2}, g x ∂μ) -
          (∫ x, g x ∂μ) / 2)
      rw [map_neg, hgg]
      ring
  obtain ⟨p, hp, hz⟩ := exists_ne_zero_eq_zero_of_odd F hF hodd
  have hbisf : (∫ x in {x : E | inner ℝ (J p.1) x ≤ p.2}, f x ∂μ) =
      (∫ x, f x ∂μ) / 2 := by
    have h := congrArg Complex.re hz
    change A f (P p) - (∫ x, f x ∂μ) / 2 = 0 at h
    linarith
  have hbisg : (∫ x in {x : E | inner ℝ (J p.1) x ≤ p.2}, g x ∂μ) =
      (∫ x, g x ∂μ) / 2 := by
    have h := congrArg Complex.im hz
    change A g (P p) - (∫ x, g x ∂μ) / 2 = 0 at h
    linarith
  refine ⟨J p.1, p.2, ?_, hbisf, hbisg⟩
  intro hv
  by_cases ht : 0 ≤ p.2
  · have heq : {x : E | inner ℝ (J p.1) x ≤ p.2} = univ := by simp [hv, ht]
    rw [heq, setIntegral_univ] at hbisf
    apply htotal
    linarith
  · have heq : {x : E | inner ℝ (J p.1) x ≤ p.2} = ∅ := by simp [hv, ht]
    rw [heq, setIntegral_empty] at hbisf
    apply htotal
    linarith
)

/-- Every integrable real-valued function admits a bisecting hyperplane
through a prescribed pivot, with nonzero normal in a prescribed
injectively parametrized real two-plane.

This isolates the rotation argument in [LS93, Lemma 2.5, proof of Claim 1].
The formulation uses an explicit continuous linear parametrization of the
normal plane and extends the source's continuous Lebesgue-density setting
to integrable signed functions against Haar measure. The total integral
may vanish.

**Proof sketch.** On the complex unit circle, subtract half the total
integral from the integral over the cut with normal `J z` and threshold
`inner (J z) c`. Injectivity makes every normal nonzero, so half-space
integral continuity makes this scalar map continuous. The opposite-cut
identity makes it odd. Its values at opposite points bracket zero;
the intermediate value theorem on the connected circle supplies a zero. -/
theorem exists_pivot_hyperplane_bisect_integral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (c : E) (f : E → ℝ) (hf : Integrable f μ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      (∫ x in {x : E | inner ℝ (J z) x ≤ inner ℝ (J z) c}, f x ∂μ) =
        (∫ x, f x ∂μ) / 2 :=
  (by
  have hnormal (z : Circle) : J (z : ℂ) ≠ 0 := by
    intro h
    exact Circle.coe_ne_zero z (hJ (h.trans J.map_zero.symm))
  let P : Circle → E × ℝ := fun z => (J (z : ℂ), inner ℝ (J (z : ℂ)) c)
  have hP : Continuous P :=
    (J.continuous.comp continuous_subtype_val).prodMk
      ((J.continuous.comp continuous_subtype_val).inner continuous_const)
  have hPne (z : Circle) : P z ≠ (0, 0) := by
    intro h
    exact hnormal z (congrArg Prod.fst h)
  let F : Circle → ℝ := fun z =>
    (∫ x in {x : E | inner ℝ (J (z : ℂ)) x ≤ inner ℝ (J (z : ℂ)) c}, f x ∂μ) -
      (∫ x, f x ∂μ) / 2
  have hF : Continuous F :=
    ((continuousOn_integral_halfspace μ f hf).comp_continuous hP hPne).sub continuous_const
  let m : Circle := ⟨(-1 : ℂ), mem_sphere_zero_iff_norm.mpr (by simp)⟩
  have hneg : F m = -F 1 := by
    have hb := measure_inner_eq_zero_of_pair_ne_zero μ (J (1 : ℂ))
      (inner ℝ (J (1 : ℂ)) c) (hPne 1)
    have hcut := integral_halfspace_neg_eq_sub μ f hf (J (1 : ℂ))
      (inner ℝ (J (1 : ℂ)) c) hb
    change (∫ x in {x : E | inner ℝ (J (-1)) x ≤ inner ℝ (J (-1)) c}, f x ∂μ) -
        (∫ x, f x ∂μ) / 2 =
      -((∫ x in {x : E | inner ℝ (J 1) x ≤ inner ℝ (J 1) c}, f x ∂μ) -
        (∫ x, f x ∂μ) / 2)
    rw [map_neg, inner_neg_left, hcut]
    ring
  have hsurj : Function.Surjective Circle.exp := fun z =>
    ⟨(z : ℂ).arg, Circle.exp_arg z⟩
  letI : ConnectedSpace Circle := hsurj.connectedSpace Circle.exp.continuous
  have hzero : ∃ z : Circle, F z = 0 := by
    by_cases h : F 1 ≤ 0
    · apply intermediate_value_univ 1 m hF
      exact ⟨h, by rw [hneg]; linarith⟩
    · apply intermediate_value_univ m 1 hF
      exact ⟨by rw [hneg]; linarith, le_of_not_ge h⟩
  obtain ⟨z, hz⟩ := hzero
  refine ⟨(z : ℂ), Circle.norm_coe z, ?_⟩
  change (∫ x in {x : E | inner ℝ (J (z : ℂ)) x ≤ inner ℝ (J (z : ℂ)) c}, f x ∂μ) -
    (∫ x, f x ∂μ) / 2 = 0 at hz
  linarith
)

/-- Given two integrable real-valued functions whose second total integral
is positive, one can choose a cut through a prescribed pivot with normal
in a prescribed real two-plane that bisects the first integral and keeps
the second integral positive.

This isolates the side-selection step in [LS93, Lemma 2.5, proof of Claim 1],
using an explicit continuous linear parametrization of the normal plane
and integrable signed functions against Haar measure. Positivity of the
first total, assumed in the localization application, is unnecessary here.

**Proof sketch.** Choose a unit parameter giving a bisecting cut for the
first function. If its second-function integral is positive, retain it.
Otherwise negate the parameter. The opposite-cut identity makes the new
second integral its positive total minus a nonpositive integral, while
preserving bisection of the first integral and the pivot constraint. -/
theorem exists_pivot_hyperplane_bisect_integral_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (c : E) (f g : E → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hgpos : 0 < ∫ x, g x ∂μ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      (∫ x in {x : E | inner ℝ (J z) x ≤ inner ℝ (J z) c}, f x ∂μ) =
        (∫ x, f x ∂μ) / 2 ∧
      0 < ∫ x in {x : E | inner ℝ (J z) x ≤ inner ℝ (J z) c}, g x ∂μ :=
  (by
  obtain ⟨z, hz, hbis⟩ := exists_pivot_hyperplane_bisect_integral μ J hJ c f hf
  by_cases hpos : 0 < ∫ x in {x : E | inner ℝ (J z) x ≤ inner ℝ (J z) c}, g x ∂μ
  · exact ⟨z, hz, hbis, hpos⟩
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      norm_num at hz
    have hn : J z ≠ 0 := fun h => hz0 (hJ (h.trans J.map_zero.symm))
    have hb := measure_inner_eq_zero_of_pair_ne_zero μ (J z) (inner ℝ (J z) c)
      (fun h => hn (congrArg Prod.fst h))
    have hff := integral_halfspace_neg_eq_sub μ f hf (J z) (inner ℝ (J z) c) hb
    have hgg := integral_halfspace_neg_eq_sub μ g hg (J z) (inner ℝ (J z) c) hb
    refine ⟨-z, ?_, ?_, ?_⟩
    · simpa only [norm_neg] using hz
    · rw [map_neg, inner_neg_left, hff]
      linarith
    · rw [map_neg, inner_neg_left, hgg]
      have := le_of_not_gt hpos
      linarith
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
