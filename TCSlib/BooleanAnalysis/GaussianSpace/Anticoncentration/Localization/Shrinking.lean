/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Geometry
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shrinking convex sets by prescribed cuts

## Main definitions

No new definitions.

## Main results

* `exists_antitone_compact_convex_collinear_iInter`: preserving cuts through
  prescribed coordinate pivots yield nested convex sets with a collinear intersection.
* `exists_antitone_compact_convex_collinear_iInter_euclidean`: transport of
  the construction to Euclidean space through its coordinate equivalence.

## References

* [LS93] L. Lovász and M. Simonovits, *Random Walks in a Convex Body and an
  Improved Volume Algorithm*, Random Structures & Algorithms 4(4) (1993),
  359–412, Lemma 2.5, proof of Claim 1, pp. 379–380.
-/

open Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- A compact convex set can be shrunk to a nonempty collinear intersection
while preserving a predicate at every finite stage, if that predicate
ensures nonemptiness and can be preserved by a coordinate half-space cut
through every prescribed rational pivot.

This abstracts the cutting invariant in [LS93, Lemma 2.5, proof of Claim 1,
pp.379–380] to a predicate with an explicit one-step cut hypothesis.
It does not assert preservation of the predicate at the limiting set.

**Proof sketch.** If the initial set is collinear, take the constant sequence.
Otherwise distinct coordinate indices exist. Enumerate all pairs of distinct
coordinates and rational pivots, and recursively choose a preserving cut for
each constraint. Closed half-space intersection preserves compactness and
convexity, and the predicate ensures nonemptiness at every stage. Compact
nesting gives a nonempty intersection. This convex intersection satisfies
every prescribed rational-coordinate half-space condition, so the rational
half-space criterion forces it to be collinear. -/
theorem exists_antitone_compact_convex_collinear_iInter
    {n : ℕ} (P : Set (Fin n → ℝ) → Prop)
    (K₀ : Set (Fin n → ℝ)) (hK₀compact : IsCompact K₀)
    (hK₀convex : Convex ℝ K₀) (hPK₀ : P K₀)
    (hnonempty : ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → P K → K.Nonempty)
    (hcut : ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → P K →
      ∀ i j : Fin n, i ≠ j → ∀ q : ℚ × ℚ,
        ∃ ℓ : (ℝ × ℝ) →ₗ[ℝ] ℝ, ℓ ≠ 0 ∧
          P (K ∩ {x : Fin n → ℝ |
            ℓ (x i, x j) ≤ ℓ ((q.1 : ℝ), (q.2 : ℝ))})) :
    ∃ K : ℕ → Set (Fin n → ℝ),
      K 0 = K₀ ∧ Antitone K ∧
      (∀ m : ℕ, IsCompact (K m) ∧ Convex ℝ (K m) ∧ P (K m)) ∧
      (⋂ m : ℕ, K m).Nonempty ∧
      Collinear ℝ (⋂ m : ℕ, K m) :=
  (by
  classical
  by_cases hcol : Collinear ℝ K₀
  · refine ⟨fun _ => K₀, rfl, fun _ _ _ => Subset.rfl, fun _ => ⟨hK₀compact, hK₀convex, hPK₀⟩, ?_, ?_⟩
    · simpa using hnonempty K₀ hK₀compact hK₀convex hPK₀
    · exact hcol.subset (iInter_subset (fun _ : ℕ => K₀) 0)
  obtain ⟨i, j, hij, _⟩ := exists_coordinate_projection_interior_nonempty hK₀convex hcol
  let C := {ij : Fin n × Fin n // ij.1 ≠ ij.2} × (ℚ × ℚ)
  letI : Nonempty C := ⟨(⟨(i, j), hij⟩, (0, 0))⟩
  obtain ⟨e, he⟩ := exists_surjective_nat C
  let T := {K : Set (Fin n → ℝ) // IsCompact K ∧ Convex ℝ K ∧ P K}
  let R (c : C) : (Fin n → ℝ) →ₗ[ℝ] ℝ × ℝ :=
    (LinearMap.proj c.1.val.1).prod (LinearMap.proj c.1.val.2)
  have hchoose (s : T) (c : C) := hcut s.val s.property.1 s.property.2.1 s.property.2.2
    c.1.val.1 c.1.val.2 c.1.property c.2
  let L (s : T) (c : C) := Classical.choose (hchoose s c)
  have hL (s : T) (c : C) := Classical.choose_spec (hchoose s c)
  let H (s : T) (c : C) : Set (Fin n → ℝ) :=
    {x | L s c (R c x) ≤ L s c ((c.2.1 : ℝ), (c.2.2 : ℝ))}
  have hHclosed (s : T) (c : C) : IsClosed (H s c) :=
    isClosed_le ((L s c).comp (R c)).continuous_of_finiteDimensional continuous_const
  have hHconvex (s : T) (c : C) : Convex ℝ (H s c) :=
    (convex_Iic _).linear_preimage ((L s c).comp (R c))
  let step (s : T) (c : C) : T :=
    ⟨s.val ∩ H s c, s.property.1.inter_right (hHclosed s c),
      s.property.2.1.inter (hHconvex s c), (hL s c).2⟩
  let s : ℕ → T := Nat.rec ⟨K₀, hK₀compact, hK₀convex, hPK₀⟩ (fun m t => step t (e m))
  let K (m : ℕ) := (s m).val
  have hs (m : ℕ) : K (m + 1) = K m ∩ H (s m) (e m) := rfl
  have hdec (m : ℕ) : K (m + 1) ⊆ K m := by
    rw [hs]
    exact inter_subset_left
  have hanti : Antitone K := antitone_nat_of_succ_le hdec
  have hnon (m : ℕ) : (K m).Nonempty :=
    hnonempty _ (s m).property.1 (s m).property.2.1 (s m).property.2.2
  refine ⟨K, rfl, hanti, fun m => (s m).property, ?_, ?_⟩
  · exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hdec hnon
      (s 0).property.1 (fun m => (s m).property.1.isClosed)
  · apply collinear_of_rational_coordinate_halfspaces (convex_iInter fun m => (s m).property.2.1)
    intro i j hij q
    obtain ⟨m, hm⟩ := he (⟨(i, j), hij⟩, q)
    refine ⟨L (s m) (e m), (hL (s m) (e m)).1, ?_⟩
    intro x hx
    have hxm : x ∈ K (m + 1) := mem_iInter.mp hx (m + 1)
    rw [hs] at hxm
    have hbound := hxm.2
    change L (s m) (e m) (R (e m) x) ≤
      L (s m) (e m) (((e m).2.1 : ℝ), ((e m).2.2 : ℝ)) at hbound
    simpa only [hm] using hbound
)

/-- A compact convex set in real Euclidean space can be shrunk to a
nonempty collinear intersection while preserving a predicate at every
finite stage, if the predicate ensures nonemptiness and is preservable
by a coordinate half-space cut through each prescribed rational pivot.

This transports the abstract cutting-invariant formulation of
[LS93, Lemma 2.5, proof of Claim 1, pp.379–380] from ordinary coordinate
space to Euclidean space. It does not assert the predicate at the limit.

**Proof sketch.** Use the continuous linear coordinate equivalence from
Euclidean space to ordinary real coordinate space. Transport the predicate
by preimage and the initial set by image. Coordinates, compactness,
convexity, and the cut condition are preserved, so apply the existing
shrinking theorem. Pull the resulting sequence back through the
equivalence. Preimages preserve nesting and intersections, and the inverse
linear map transports a line containing the intersection. No measure
transport is needed. -/
theorem exists_antitone_compact_convex_collinear_iInter_euclidean
    {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)) → Prop)
    (K₀ : Set (EuclideanSpace ℝ (Fin n))) (hK₀compact : IsCompact K₀)
    (hK₀convex : Convex ℝ K₀) (hPK₀ : P K₀)
    (hnonempty : ∀ K : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact K → Convex ℝ K → P K → K.Nonempty)
    (hcut : ∀ K : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact K → Convex ℝ K → P K →
      ∀ i j : Fin n, i ≠ j → ∀ q : ℚ × ℚ,
        ∃ ℓ : (ℝ × ℝ) →ₗ[ℝ] ℝ, ℓ ≠ 0 ∧
          P (K ∩ {x : EuclideanSpace ℝ (Fin n) |
            ℓ (x i, x j) ≤ ℓ ((q.1 : ℝ), (q.2 : ℝ))})) :
    ∃ K : ℕ → Set (EuclideanSpace ℝ (Fin n)),
      K 0 = K₀ ∧ Antitone K ∧
      (∀ m : ℕ, IsCompact (K m) ∧ Convex ℝ (K m) ∧ P (K m)) ∧
      (⋂ m : ℕ, K m).Nonempty ∧
      Collinear ℝ (⋂ m : ℕ, K m) :=
  (by
  classical
  let T := EuclideanSpace.equiv (Fin n) ℝ
  let Q (A : Set (Fin n → ℝ)) : Prop := P (T ⁻¹' A)
  have hprecompact {A : Set (Fin n → ℝ)} (hA : IsCompact A) :
      IsCompact (T ⁻¹' A) := T.toHomeomorph.isCompact_preimage.mpr hA
  have hpreconvex {A : Set (Fin n → ℝ)} (hA : Convex ℝ A) :
      Convex ℝ (T ⁻¹' A) := hA.linear_preimage T.toLinearMap
  have hinit : Q (Set.image T K₀) := by
    change P (T ⁻¹' Set.image T K₀)
    simpa only [Set.preimage_image_eq _ T.injective] using hPK₀
  have hnon : ∀ A, IsCompact A → Convex ℝ A → Q A → A.Nonempty := by
    intro A hAc hAv hP
    obtain ⟨x, hx⟩ := hnonempty _ (hprecompact hAc) (hpreconvex hAv) hP
    exact ⟨T x, hx⟩
  have hcuts : ∀ A, IsCompact A → Convex ℝ A → Q A →
      ∀ i j : Fin n, i ≠ j → ∀ q : ℚ × ℚ,
        ∃ ℓ : (ℝ × ℝ) →ₗ[ℝ] ℝ, ℓ ≠ 0 ∧
          Q (A ∩ {x | ℓ (x i, x j) ≤ ℓ ((q.1 : ℝ), (q.2 : ℝ))}) := by
    intro A hAc hAv hP i j hij q
    obtain ⟨ℓ, hℓ, hcutP⟩ := hcut _ (hprecompact hAc) (hpreconvex hAv) hP i j hij q
    exact ⟨ℓ, hℓ, hcutP⟩
  obtain ⟨A, hA0, hanti, hA, hne, hcol⟩ :=
    exists_antitone_compact_convex_collinear_iInter Q (Set.image T K₀)
      (hK₀compact.image T.continuous) (hK₀convex.linear_image T.toLinearMap)
      hinit hnon hcuts
  let K (m : ℕ) := T ⁻¹' A m
  have hlim : (⋂ m, K m) = T ⁻¹' (⋂ m, A m) := by
    ext x
    simp only [K, Set.mem_iInter, Set.mem_preimage]
  refine ⟨K, ?_, ?_, ?_, ?_, ?_⟩
  · change T ⁻¹' A 0 = K₀
    rw [hA0, Set.preimage_image_eq _ T.injective]
  · intro a b hab
    exact Set.preimage_mono (hanti hab)
  · intro m
    exact ⟨hprecompact (hA m).1, hpreconvex (hA m).2.1, (hA m).2.2⟩
  · obtain ⟨x, hx⟩ := hne
    rw [hlim]
    refine ⟨T.symm x, ?_⟩
    simpa only [Set.mem_preimage, T.apply_symm_apply] using hx
  · obtain ⟨p, v, hline⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hcol
    apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
    refine ⟨T.symm p, T.symm v, ?_⟩
    intro x hx
    rw [hlim] at hx
    obtain ⟨r, hr⟩ := hline (T x) hx
    refine ⟨r, ?_⟩
    change x = r • T.symm v + T.symm p
    apply T.injective
    change T x = r • v + p at hr
    simpa only [map_add, map_smul, T.apply_symm_apply] using hr
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
