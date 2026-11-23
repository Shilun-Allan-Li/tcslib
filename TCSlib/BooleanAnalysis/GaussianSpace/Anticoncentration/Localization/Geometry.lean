/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order.Compact

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coordinate projections for geometric localization

## Main definitions

No new definitions.

## Main results

* `exists_coordinate_det_ne_zero_of_linearIndependent`: independent coordinate
  vectors have a nonzero two-coordinate determinant.
* `exists_coordinate_projection_interior_nonempty`: a noncollinear convex set
  has a two-coordinate projection with nonempty interior.
* `exists_mem_lt_apply_of_mem_interior`: a nonzero linear functional increases
  somewhere in a set from any of its interior points.
* `collinear_of_rational_coordinate_halfspaces`: cuts through every rational
  coordinate pivot force a convex set to be collinear.
* `exists_eq_segment_of_nonempty_isCompact_convex_collinear`: a nonempty
  compact convex collinear set is a closed segment, allowing equal endpoints.

## References

* [LS93] L. Lovász and M. Simonovits, *Random Walks in a Convex Body and an
  Improved Volume Algorithm*, Random Structures & Algorithms 4(4) (1993),
  359–412, Lemma 2.5, proof of Claim 1, p. 380.
* Mathlib, `Mathlib.Topology.Algebra.Module.FiniteDimension`:
  openness of surjective linear maps with finite-dimensional codomain.
-/

open Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- Two linearly independent real coordinate vectors have a nonzero
two-coordinate determinant at distinct indices.

This is technical linear-algebra glue for finding a two-dimensional
coordinate projection; the index type need not be finite.

**Proof sketch.** Choose a coordinate where the first vector is nonzero.
If every determinant involving this coordinate vanished, the second
vector would be the first multiplied by the ratio of their values at
that coordinate, contradicting linear independence. A nonzero determinant
cannot use the same coordinate twice. -/
theorem exists_coordinate_det_ne_zero_of_linearIndependent
    {ι : Type*} (u v : ι → ℝ)
    (h : LinearIndependent ℝ ![u, v]) :
    ∃ i j : ι, i ≠ j ∧ u i * v j - u j * v i ≠ 0 :=
  (by
  classical
  have hu : u ≠ 0 := by
    simpa using (LinearIndependent.ne_zero (0 : Fin 2) h)
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra! hz
    exact hu (funext hz)
  have hex : ∃ j, u i * v j - u j * v i ≠ 0 := by
    by_contra! hz
    apply (LinearIndependent.pair_iff' hu).mp h (v i / u i)
    funext j
    change (v i / u i) * u j = v j
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hi).mpr
    nlinarith [hz j]
  obtain ⟨j, hj⟩ := hex
  refine ⟨i, j, ?_, hj⟩
  intro hij
  subst j
  exact hj (by ring)
)

/-- A noncollinear convex subset of real coordinate space has a
two-coordinate projection with nonempty interior.

This isolates the coordinate-projection dimension witness used in
[LS93, Lemma 2.5, proof of Claim 1, p.380].

**Proof sketch.** Choose three noncollinear points. Their two difference
vectors are linearly independent, so some two-coordinate determinant is
nonzero: otherwise, choosing a nonzero coordinate of one vector would
force the other to be its scalar multiple. The projected three points
therefore span the coordinate plane affinely. Their convex hull lies in
the projected set, whose convexity and full affine span imply nonempty
interior. -/
theorem exists_coordinate_projection_interior_nonempty
    {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : Convex ℝ S) (hnot : ¬ Collinear ℝ S) :
    ∃ i j : Fin n, i ≠ j ∧
      (interior
        (Set.image (fun x : Fin n → ℝ => (x i, x j)) S)).Nonempty :=
  (by
  classical
  have hne : S.Nonempty := by
    by_contra h
    apply hnot
    rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact collinear_empty ℝ _
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨x₁, hx₁, hx₁₀⟩ : ∃ x₁ ∈ S, x₁ ≠ x₀ := by
    by_contra! h
    apply hnot
    apply (collinear_iff_of_mem hx₀).mpr
    refine ⟨0, ?_⟩
    intro x hx
    refine ⟨0, ?_⟩
    simpa only [zero_smul, zero_vadd] using h x hx
  obtain ⟨x₂, hx₂, hind⟩ :
      ∃ x₂ ∈ S, LinearIndependent ℝ ![x₁ - x₀, x₂ - x₀] := by
    by_contra! h
    apply hnot
    apply (collinear_iff_of_mem hx₀).mpr
    refine ⟨x₁ - x₀, ?_⟩
    intro x hx
    have hdep := h x hx
    rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr hx₁₀)] at hdep
    push_neg at hdep
    obtain ⟨r, hr⟩ := hdep
    refine ⟨r, ?_⟩
    change x = r • (x₁ - x₀) + x₀
    rw [hr, sub_add_cancel]
  obtain ⟨i, j, hij, hdet⟩ :=
    exists_coordinate_det_ne_zero_of_linearIndependent (x₁ - x₀) (x₂ - x₀) hind
  let R : (Fin n → ℝ) →ₗ[ℝ] ℝ × ℝ :=
    (LinearMap.proj i).prod (LinearMap.proj j)
  let q : Fin 3 → ℝ × ℝ := ![R x₀, R x₁, R x₂]
  have hq : ¬ Collinear ℝ (Set.range q) := by
    intro hc
    obtain ⟨w, hw⟩ := (collinear_iff_of_mem (show R x₀ ∈ Set.range q from ⟨0, rfl⟩)).mp hc
    obtain ⟨a, ha⟩ := hw (R x₁) ⟨1, rfl⟩
    obtain ⟨b, hb⟩ := hw (R x₂) ⟨2, rfl⟩
    have ha₁ : x₁ i = a * w.1 + x₀ i := congrArg Prod.fst ha
    have ha₂ : x₁ j = a * w.2 + x₀ j := congrArg Prod.snd ha
    have hb₁ : x₂ i = b * w.1 + x₀ i := congrArg Prod.fst hb
    have hb₂ : x₂ j = b * w.2 + x₀ j := congrArg Prod.snd hb
    apply hdet
    change (x₁ i - x₀ i) * (x₂ j - x₀ j) -
      (x₁ j - x₀ j) * (x₂ i - x₀ i) = 0
    rw [ha₁, ha₂, hb₁, hb₂]
    ring
  have haff : AffineIndependent ℝ q := affineIndependent_iff_not_collinear.mpr hq
  have hspan : affineSpan ℝ (Set.range q) = ⊤ :=
    haff.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
  have hrange : Set.range q ⊆ Set.image R S := by
    rintro y ⟨k, rfl⟩
    fin_cases k
    · exact ⟨x₀, hx₀, rfl⟩
    · exact ⟨x₁, hx₁, rfl⟩
    · exact ⟨x₂, hx₂, rfl⟩
  have hfull : affineSpan ℝ (Set.image R S) = ⊤ := by
    have h := affineSpan_mono ℝ hrange
    rw [hspan] at h
    exact top_unique h
  exact ⟨i, j, hij, (hS.linear_image R).interior_nonempty_iff_affineSpan_eq_top.mpr hfull⟩
)

/-- A nonzero real linear functional takes a value strictly greater than
its value at any prescribed interior point of a set.

No continuity assumption on the functional, convexity of the set, or
finite-dimensionality of the ambient space is required. This is technical
neighborhood glue for cuts through interior pivots.

**Proof sketch.** A nonzero scalar-valued linear map is surjective and
is open because its codomain is finite-dimensional. The image of the set
is therefore a neighborhood of the functional's value at the interior
point. Choose a strictly greater real number in that neighborhood and
lift it to a point of the set. -/
theorem exists_mem_lt_apply_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {c : E}
    (hc : c ∈ interior S) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ x ∈ S, ℓ c < ℓ x :=
  (by
  have hopen := ℓ.isOpenMap_of_finiteDimensional (LinearMap.surjective_iff_ne_zero.mpr hℓ)
  have hn := hopen.image_mem_nhds (mem_interior_iff_mem_nhds.mp hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hy : ℓ c + δ / 2 ∈ Set.image ℓ S := hball (by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    linarith)
  obtain ⟨x, hx, hxeq⟩ := hy
  exact ⟨x, hx, by rw [hxeq]; linarith⟩
)

/-- A convex subset of real coordinate space is collinear if every
two-coordinate projection lies in a closed half-plane through each
rational pivot, with a nonzero normal allowed to depend on that pivot.

This isolates the final geometric contradiction in [LS93, Lemma 2.5,
proof of Claim 1, p.380]. Unlike its application to nested compact bodies,
this implication needs no compactness, closedness, or nonemptiness assumption.

**Proof sketch.** If the set were noncollinear, some two-coordinate
projection would have nonempty interior. Density of rational pairs gives
a rational pivot in that interior. A nonzero functional defining the
assumed containing half-plane must take a strictly greater value at
some point of the projected set than at its interior pivot, contradicting
the half-plane bound. -/
theorem collinear_of_rational_coordinate_halfspaces
    {n : ℕ} {S : Set (Fin n → ℝ)} (hS : Convex ℝ S)
    (hcuts : ∀ i j : Fin n, i ≠ j → ∀ q : ℚ × ℚ,
      ∃ ℓ : (ℝ × ℝ) →ₗ[ℝ] ℝ, ℓ ≠ 0 ∧
        ∀ x ∈ S, ℓ (x i, x j) ≤ ℓ ((q.1 : ℝ), (q.2 : ℝ))) :
    Collinear ℝ S :=
  (by
  by_contra hnot
  obtain ⟨i, j, hij, hint⟩ := exists_coordinate_projection_interior_nonempty hS hnot
  have hd : Dense (Set.range (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  obtain ⟨y, ⟨q, rfl⟩, hq⟩ := hd.exists_mem_open isOpen_interior hint
  obtain ⟨ℓ, hℓ, hbound⟩ := hcuts i j hij q
  obtain ⟨z, ⟨x, hx, rfl⟩, hlt⟩ := exists_mem_lt_apply_of_mem_interior hq ℓ hℓ
  exact (not_lt_of_ge (hbound x hx)) hlt
)

/-- Every nonempty compact convex collinear subset of a real normed
vector space is a closed segment, possibly with equal endpoints.

This isolates the endpoint representation of the limiting set in
[LS93, Lemma 2.5, proof of Claim 1, pp.379–380]. The ambient space need
not be finite-dimensional or complete.

**Proof sketch.** Choose two points of the compact set maximizing their
distance. Any other point is collinear with them, so one of the three
points lies between the other two. If the new point is not between the
chosen endpoints, the distance-addition formula and maximality force it
to equal an endpoint. This proves containment in the segment; convexity
gives the reverse containment. -/
theorem exists_eq_segment_of_nonempty_isCompact_convex_collinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hne : K.Nonempty) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) (hcollinear : Collinear ℝ K) :
    ∃ a b : E, K = segment ℝ a b :=
  (by
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hmax⟩ := (hcompact.prod hcompact).exists_isMaxOn
    (hne.prod hne) (show ContinuousOn (fun p : E × E => dist p.1 p.2) (K ×ˢ K) from
      (continuous_fst.dist continuous_snd).continuousOn)
  refine ⟨a, b, Set.Subset.antisymm ?_ (hconvex.segment_subset ha hb)⟩
  intro x hx
  have hthree : Collinear ℝ ({a, x, b} : Set E) :=
    hcollinear.subset (by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨ha, hx, hb⟩)
  rcases hthree.wbtw_or_wbtw_or_wbtw with hbetween | hbetween | hbetween
  · exact mem_segment_iff_wbtw.mpr hbetween
  · have hd := hbetween.dist_add_dist
    have hm : dist x a ≤ dist a b := hmax (show (x, a) ∈ K ×ˢ K from ⟨hx, ha⟩)
    have hxb : dist x b = 0 := by
      rw [dist_comm b a] at hd
      linarith [(dist_nonneg : 0 ≤ dist x b)]
    have hxb' : x = b := dist_eq_zero.mp hxb
    rw [hxb']
    exact right_mem_segment ℝ a b
  · have hd := hbetween.dist_add_dist
    have hm : dist b x ≤ dist a b := hmax (show (b, x) ∈ K ×ˢ K from ⟨hb, hx⟩)
    have hax : dist a x = 0 := by
      rw [dist_comm b a] at hd
      linarith [(dist_nonneg : 0 ≤ dist a x)]
    have hax' : a = x := dist_eq_zero.mp hax
    rw [← hax']
    exact left_mem_segment ℝ a b
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
