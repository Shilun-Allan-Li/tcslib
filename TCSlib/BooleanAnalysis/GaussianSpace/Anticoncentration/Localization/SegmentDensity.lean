/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.DensityLimit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concave profiles on limiting segments

## Main definitions

No new definitions.

## Main results

* `exists_concave_profile_of_iInter_eq_segment`: nested compact convex
  bodies with positive integrals of two continuous signed tests yield
  a nonzero concave profile on their nondegenerate limiting segment.

## References

* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, proof of Claim 2, pp.380–381.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- Nested compact convex bodies shrinking to a nondegenerate segment,
with positive integrals of two continuous signed tests at every stage,
yield a nonzero midpoint-normalized concave profile giving nonnegative
weighted integrals of both tests along the segment.
[LS93, Lemma 2.5, proof of Claim 2, pp.380–381]

The ambient coordinate dimension is one more than the positive
transverse dimension. The segment is parametrized by its ordered
endpoints on the unit interval. The profile is concave only on the
open unit interval, has midpoint value one, and has values between
zero and two there. It is not asserted to have integral one.
This extends the fixed affine-graph formulation by an invertible
affine coordinate change.

**Proof sketch.** Choose a coordinate distinguishing the endpoints.
Translate the first endpoint to zero, scale every coordinate by the
inverse of the selected endpoint difference, move the selected
coordinate to the first position, and split off that coordinate.
The endpoints become zero and a point with first coordinate one, so
the limiting segment is an affine graph over the unit interval.
This affine homeomorphism preserves compactness, convexity and nesting.
Its coordinate permutation and splitting preserve volume, while its
translation and homothety change each signed integral by one common
positive absolute Jacobian factor. Transport both tests and apply the
fixed-graph concave-profile theorem. The inverse affine map carries
the normalized graph parametrization back to the original segment
parametrization, giving the two claimed inequalities. -/
theorem exists_concave_profile_of_iInter_eq_segment
    {n : ℕ} (hn : 1 ≤ n)
    (K : ℕ → Set (Fin (n + 1) → ℝ))
    (hcompact : ∀ m : ℕ, IsCompact (K m))
    (hconvex : ∀ m : ℕ, Convex ℝ (K m))
    (hanti : Antitone K)
    (a b : Fin (n + 1) → ℝ) (hab : a ≠ b)
    (hinter : (⋂ m : ℕ, K m) = segment ℝ a b)
    (F G : (Fin (n + 1) → ℝ) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hFpos : ∀ m : ℕ, 0 < ∫ x in K m, F x)
    (hGpos : ∀ m : ℕ, 0 < ∫ x in K m, G x) :
    ∃ φ : ℝ → ℝ,
      ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) φ ∧
      φ (1 / 2 : ℝ) = 1 ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, φ t ∈ Set.Icc (0 : ℝ) 2) ∧
      0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1,
        (φ t) ^ n * F (AffineMap.lineMap a b t) ∧
      0 ≤ ∫ t in Set.Ioo (0 : ℝ) 1,
        (φ t) ^ n * G (AffineMap.lineMap a b t) :=
  (by
  classical
  -- Normalize the distinguished coordinate with a volume-preserving split.
  obtain ⟨i, hi⟩ : ∃ i, b i - a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hab (funext (fun i => (sub_eq_zero.mp (h i)).symm))
  let d := b i - a i
  have hd : d ≠ 0 := hi
  let P := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (n + 1) => ℝ) (Equiv.swap 0 i)
  let L : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).trans P
  have hLi (z : ℝ × (Fin n → ℝ)) : L z i = z.1 := by
    change (Equiv.piCongrLeft (fun _ : Fin (n + 1) => ℝ) (Equiv.swap 0 i))
      (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 z.2) i = z.1
    simpa only [Equiv.swap_apply_left, Fin.cons_zero] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin (n + 1) => ℝ)
        (e := Equiv.swap 0 i) (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 z.2) 0)
  let e := L.toHomeomorph.trans
    ((Homeomorph.smul (Units.mk0 d hd)).trans (Homeomorph.addLeft a))
  have he (z : ℝ × (Fin n → ℝ)) : e z = a + d • L z := rfl
  have hLm : MeasurePreserving L := by
    have hP := volume_measurePreserving_piCongrLeft
      (fun _ : Fin (n + 1) => ℝ) (Equiv.swap 0 i)
    have hcons := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have hcons' : MeasurePreserving (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)) := by
      convert hcons using 1
      ext z k
      change Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 z.2 k =
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) 0) z k
      rw [Fin.insertNthEquiv_zero]
      rfl
    exact hP.comp hcons'

  -- The inverse normalization parametrizes the segment by an affine graph.
  let z := L.symm (d⁻¹ • (b - a))
  have hz : z.1 = 1 := by
    rw [← hLi z]
    change (L (L.symm (d⁻¹ • (b - a)))) i = 1
    rw [L.apply_symm_apply]
    change d⁻¹ * (b i - a i) = 1
    exact inv_mul_cancel₀ hd
  have hparam (t : ℝ) : e (t, t • z.2) = AffineMap.lineMap a b t := by
    have ht : (t, t • z.2) = t • z := by
      apply Prod.ext
      · change t = t * z.1
        rw [hz, mul_one]
      · rfl
    rw [he, ht, map_smul]
    change a + d • (t • L (L.symm (d⁻¹ • (b - a)))) = _
    rw [L.apply_symm_apply, AffineMap.lineMap_apply_module', add_comm (t • (b - a)) a]
    simp only [smul_smul]
    congr 1
    rw [mul_left_comm d t d⁻¹, mul_inv_cancel₀ hd, mul_one]
  let B (m : ℕ) := e ⁻¹' K m
  have hBc (m : ℕ) : IsCompact (B m) := e.isCompact_preimage.mpr (hcompact m)
  have hBv (m : ℕ) : Convex ℝ (B m) := by
    intro x hx y hy α β hα hβ hsum
    have h := hconvex m hx hy hα hβ hsum
    change e (α • x + β • y) ∈ K m
    convert h using 1
    rw [he, he, he, map_add, map_smul, map_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun r : ℝ => r * a k) hsum]
  have hBa : Antitone B := fun j k hjk => Set.preimage_mono (hanti hjk)
  have hBi : (⋂ m, B m) =
      Set.image (fun t : ℝ => (t, (0 : Fin n → ℝ) + t • z.2)) (Set.Icc (0 : ℝ) 1) := by
    rw [show (⋂ m, B m) = e ⁻¹' (⋂ m, K m) from Set.preimage_iInter.symm,
      hinter, segment_eq_image_lineMap]
    ext p
    constructor
    · rintro ⟨t, ht, htp⟩
      refine ⟨t, ht, ?_⟩
      apply e.injective
      simpa only [zero_add, hparam] using htp
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simp only [zero_add, hparam]⟩

  -- Both signed tests acquire the same positive Haar scaling factor.
  let J := |(d ^ Module.finrank ℝ (Fin (n + 1) → ℝ))⁻¹|
  have hJ : 0 < J := abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hd))
  have htransport (T : (Fin (n + 1) → ℝ) → ℝ) (m : ℕ) :
      (∫ p in B m, T (e p)) = J * ∫ x in K m, T x := by
    rw [← integral_indicator (hBc m).measurableSet]
    have hind : (B m).indicator (fun p => T (e p)) =
        (fun p => (K m).indicator T (e p)) := by
      funext p
      exact Set.indicator_comp_right e
    rw [hind]
    simp only [he]
    rw [hLm.integral_comp L.toHomeomorph.measurableEmbedding
      (fun x => (K m).indicator T (a + d • x))]
    rw [Measure.integral_comp_smul volume (fun x => (K m).indicator T (a + x)) d,
      (measurePreserving_add_left volume a).integral_comp
        (MeasurableEquiv.addLeft a).measurableEmbedding,
      integral_indicator (hcompact m).measurableSet]
    rfl
  obtain ⟨φ, hφc, hφn, hφb, hφF, hφG⟩ :=
    exists_concave_profile_of_iInter_eq_affine_graph hn B hBc hBv hBa 0 z.2 hBi
      (fun p => F (e p)) (fun p => G (e p))
      (hF.comp e.continuous) (hG.comp e.continuous)
      (fun m => by rw [htransport]; exact mul_pos hJ (hFpos m))
      (fun m => by rw [htransport]; exact mul_pos hJ (hGpos m))
  refine ⟨φ, hφc, hφn, hφb, ?_, ?_⟩
  · simpa only [zero_add, hparam] using hφF
  · simpa only [zero_add, hparam] using hφG
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
