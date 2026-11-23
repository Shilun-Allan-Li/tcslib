/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Bisection
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Shrinking
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coordinate cuts and shrinking preserving positive integrals

## Main definitions

No new definitions.

## Main results

* `exists_coordinate_hyperplane_bisect_integral_pos`: a half-space in two
  prescribed coordinates bisects one integral and preserves positivity of another.
* `exists_antitone_compact_convex_collinear_iInter_integral_pos`: positive
  integrals survive nested cuts whose nonempty intersection is collinear.

* `exists_antitone_compact_convex_collinear_iInter_integral_pos_pi`: positive
  coordinate-space integrals persist through shrinking to a collinear set.

## References

* [LS93] L. Lovász and M. Simonovits, *Random Walks in a Convex Body and an
  Improved Volume Algorithm*, Random Structures & Algorithms 4(4) (1993),
  359–412, Lemma 2.5, proof of Claim 1, pp. 379–380.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- Given distinct coordinates in real Euclidean space and a prescribed
real planar pivot, two integrable real-valued functions whose second
total is positive admit a coordinate cut through that pivot which bisects
the first integral and keeps the second integral positive.

This is the coordinate formulation of the rotation and side-selection
step in [LS93, Lemma 2.5, proof of Claim 1, p.379]. It uses integrable
signed functions against Haar measure; the adjoint realizes the prescribed
plane of cut normals. No sign assumption on the first total is needed.

**Proof sketch.** Combine the two coordinate projections into a surjective
continuous real-linear map to the complex plane. Its adjoint is injective.
Choose an ambient pivot mapping to the prescribed planar pivot and apply
the positive-side pivot bisection theorem. Adjoint inner-product identities
express the resulting cut by a planar linear functional. The theorem's
unit parameter makes that functional nonzero. -/
theorem exists_coordinate_hyperplane_bisect_integral_pos
    {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [Measure.IsAddHaarMeasure μ]
    (i j : Fin n) (hij : i ≠ j) (q : ℝ × ℝ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hgpos : 0 < ∫ x, g x ∂μ) :
    ∃ ℓ : (ℝ × ℝ) →ₗ[ℝ] ℝ, ℓ ≠ 0 ∧
      (∫ x in {x | ℓ (x i, x j) ≤ ℓ q}, f x ∂μ) =
        (∫ x, f x ∂μ) / 2 ∧
      0 < ∫ x in {x | ℓ (x i, x j) ≤ ℓ q}, g x ∂μ :=
  (by
  classical
  let R : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.proj i).prod (EuclideanSpace.proj j)
  let π : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ :=
    Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp R
  have hπ : Function.Surjective π := by
    intro z
    refine ⟨EuclideanSpace.single i z.re + EuclideanSpace.single j z.im, ?_⟩
    have he : R (EuclideanSpace.single i z.re + EuclideanSpace.single j z.im) =
        Complex.equivRealProdCLM z := by
      ext <;> simp [R, hij, hij.symm]
    change Complex.equivRealProdCLM.symm (R _) = z
    rw [he, ContinuousLinearEquiv.symm_apply_apply]
  have hJ : Function.Injective π.adjoint := by
    intro z w h
    apply ext_inner_right ℝ
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    rw [← π.adjoint_inner_left x z, ← π.adjoint_inner_left x w, h]
  obtain ⟨c, hc⟩ := hπ (Complex.equivRealProdCLM.symm q)
  obtain ⟨z, hz, hfcut, hgcut⟩ :=
    exists_pivot_hyperplane_bisect_integral_pos μ π.adjoint hJ c f g hf hg hgpos
  let ℓ : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
    ((innerSL ℝ z).comp Complex.equivRealProdCLM.symm.toContinuousLinearMap).toLinearMap
  have hℓ : ℓ ≠ 0 := by
    intro h
    have hzz : inner ℝ z z = 0 := by
      have he := LinearMap.congr_fun h (Complex.equivRealProdCLM z)
      simpa [ℓ] using he
    have hz0 := inner_self_eq_zero.mp hzz
    rw [hz0, norm_zero] at hz
    norm_num at hz
  have hcut : {x | inner ℝ (π.adjoint z) x ≤ inner ℝ (π.adjoint z) c} =
      {x | ℓ (x i, x j) ≤ ℓ q} := by
    ext x
    simp only [π.adjoint_inner_left, hc]
    rfl
  exact ⟨ℓ, hℓ, hcut ▸ hfcut, hcut ▸ hgcut⟩
)

/-- Two integrable real-valued functions with positive integrals on a
compact convex set admit a nested sequence of compact convex subsets,
starting at that set, on each of which both integrals remain positive,
with nonempty collinear intersection.

This formalizes the nested-set conclusion in [LS93, Lemma 2.5, proof of
Claim 1, pp.379–380]. The functions may be signed and merely integrable,
the measure may be any Haar measure, and no nonempty-interior assumption
is imposed on the sets. Neither integral is asserted to remain positive
on the limiting intersection.

**Proof sketch.** Use positivity of both set integrals as the invariant
in the Euclidean abstract shrinking theorem. It ensures nonemptiness.
For each compact convex stage, multiply both functions by its indicator
and apply the prescribed-coordinate positive-side cut theorem. Indicator
integration identifies these cut integrals with integrals over the new
intersection. The first is half a positive integral, and the second is
positive by construction. The abstract shrinking theorem then supplies
the sequence and its nonempty collinear intersection. -/
theorem exists_antitone_compact_convex_collinear_iInter_integral_pos
    {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [Measure.IsAddHaarMeasure μ]
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (K₀ : Set (EuclideanSpace ℝ (Fin n)))
    (hK₀compact : IsCompact K₀) (hK₀convex : Convex ℝ K₀)
    (hfpos : 0 < ∫ x in K₀, f x ∂μ)
    (hgpos : 0 < ∫ x in K₀, g x ∂μ) :
    ∃ K : ℕ → Set (EuclideanSpace ℝ (Fin n)),
      K 0 = K₀ ∧ Antitone K ∧
      (∀ m : ℕ, IsCompact (K m) ∧ Convex ℝ (K m) ∧
        (0 < ∫ x in K m, f x ∂μ) ∧
        (0 < ∫ x in K m, g x ∂μ)) ∧
      (⋂ m : ℕ, K m).Nonempty ∧
      Collinear ℝ (⋂ m : ℕ, K m) :=
  (by
  apply exists_antitone_compact_convex_collinear_iInter_euclidean
    (fun K => (0 < ∫ x in K, f x ∂μ) ∧ (0 < ∫ x in K, g x ∂μ))
    K₀ hK₀compact hK₀convex ⟨hfpos, hgpos⟩
  · intro K _ _ hP
    by_contra hne
    have hK : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hK, setIntegral_empty] at hP
    exact (lt_irrefl 0) hP.1
  · intro K hKcompact _ hP i j hij q
    have hKm := hKcompact.isClosed.measurableSet
    obtain ⟨ℓ, hℓ, hhalf, hpos⟩ :=
      exists_coordinate_hyperplane_bisect_integral_pos μ i j hij
        ((q.1 : ℝ), (q.2 : ℝ)) (K.indicator f) (K.indicator g)
        (hf.indicator hKm) (hg.indicator hKm)
        (by simpa only [integral_indicator hKm] using hP.2)
    refine ⟨ℓ, hℓ, ?_, ?_⟩
    · rw [setIntegral_indicator hKm, integral_indicator hKm, Set.inter_comm] at hhalf
      rw [hhalf]
      exact half_pos hP.1
    · simpa only [setIntegral_indicator hKm, Set.inter_comm] using hpos
)

/-- Positive integrals of two real functions over a compact convex
subset of real coordinate space persist along nested compact convex
sets with a nonempty collinear intersection.
[LS93, Lemma 2.5, proof of Claim 1, pp.379–380]

No continuity or separate integrability assumption is required:
each positive restricted integral already implies restricted
integrability. The conclusion preserves positivity at every finite
stage and makes no positivity assertion about integration over the
limiting set.

**Proof sketch.** Apply the abstract shrinking theorem in coordinate
space to the property that both restricted integrals are positive.
For each requested coordinate cut, extend the functions by zero
outside the current compact set. Their positive integrals give global
integrability of these extensions. Transport them to Euclidean space
through the volume-preserving coordinate equivalence and use the
existing coordinate cut that bisects the first integral and preserves
positivity of the second. Transport the cut integrals back; coordinates
are unchanged by the equivalence. The first cut integral is half a
positive number and the second is positive, giving the required
one-step property. -/
theorem exists_antitone_compact_convex_collinear_iInter_integral_pos_pi
    {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (K₀ : Set (Fin n → ℝ))
    (hK₀compact : IsCompact K₀) (hK₀convex : Convex ℝ K₀)
    (hfpos : 0 < ∫ x in K₀, f x)
    (hgpos : 0 < ∫ x in K₀, g x) :
    ∃ K : ℕ → Set (Fin n → ℝ),
      K 0 = K₀ ∧ Antitone K ∧
      (∀ m : ℕ, IsCompact (K m) ∧ Convex ℝ (K m) ∧
        (0 < ∫ x in K m, f x) ∧
        (0 < ∫ x in K m, g x)) ∧
      (⋂ m : ℕ, K m).Nonempty ∧
      Collinear ℝ (⋂ m : ℕ, K m) :=
  (by
  apply exists_antitone_compact_convex_collinear_iInter
    (fun K => (0 < ∫ x in K, f x) ∧ (0 < ∫ x in K, g x))
    K₀ hK₀compact hK₀convex ⟨hfpos, hgpos⟩
  · intro K _ _ hP
    by_contra hne
    have hK : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hK, setIntegral_empty] at hP
    exact (lt_irrefl 0) hP.1
  · intro K hKcompact _ hP i j hij q
    have hKm := hKcompact.measurableSet
    have hf0 : Integrable (K.indicator f) :=
      Integrable.of_integral_ne_zero (by
        rw [integral_indicator hKm]
        exact ne_of_gt hP.1)
    have hg0 : Integrable (K.indicator g) :=
      Integrable.of_integral_ne_zero (by
        rw [integral_indicator hKm]
        exact ne_of_gt hP.2)
    let e := EuclideanSpace.equiv (Fin n) ℝ
    have hmp : MeasurePreserving e := PiLp.volume_preserving_ofLp (Fin n)
    have hfull (T : (Fin n → ℝ) → ℝ) :
        (∫ x : EuclideanSpace ℝ (Fin n), (K.indicator T) (e x)) = ∫ x in K, T x := by
      rw [hmp.integral_comp e.toHomeomorph.measurableEmbedding, integral_indicator hKm]
    obtain ⟨ℓ, hℓ, hhalf, hpos⟩ :=
      exists_coordinate_hyperplane_bisect_integral_pos volume i j hij
        ((q.1 : ℝ), (q.2 : ℝ))
        (fun x => (K.indicator f) (e x)) (fun x => (K.indicator g) (e x))
        (hmp.integrable_comp_of_integrable hf0) (hmp.integrable_comp_of_integrable hg0)
        (by rw [hfull]; exact hP.2)
    have hcut (T : (Fin n → ℝ) → ℝ) :
        (∫ x : EuclideanSpace ℝ (Fin n) in
          {x | ℓ (x i, x j) ≤ ℓ ((q.1 : ℝ), (q.2 : ℝ))},
          (K.indicator T) (e x)) =
        ∫ x in K ∩ {x : Fin n → ℝ | ℓ (x i, x j) ≤ ℓ ((q.1 : ℝ), (q.2 : ℝ))},
          T x := by
      change (∫ x in e ⁻¹' {x : Fin n → ℝ |
        ℓ (x i, x j) ≤ ℓ ((q.1 : ℝ), (q.2 : ℝ))}, (K.indicator T) (e x)) = _
      rw [hmp.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding,
        setIntegral_indicator hKm, Set.inter_comm]
    refine ⟨ℓ, hℓ, ?_, ?_⟩
    · rw [hcut, hfull] at hhalf
      rw [hhalf]
      exact half_pos hP.1
    · simpa only [hcut] using hpos
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
