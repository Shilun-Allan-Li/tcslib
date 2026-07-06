/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Defs.PartialOrder

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Communication Complexity Rectangles

## Main results

- `Rectangle.IsRectangle`: A subset of `X × Y` is a rectangle if it factors as `A ×ˢ B`.
- `Rectangle.IsMonochromatic`: A set is monochromatic for `g` if `g` is constant on that set.
- `Rectangle.IsFoolingSet`: A fooling set for `g` intersects every monochromatic rectangle in at most one point.
- `Rectangle.IsMonoPartition`: A monochromatic rectangle partition covers `X × Y` by disjoint monochromatic rectangles.
- `Rectangle.foolingSet_ncard_le_of_monoPartition`: Any finite monochromatic rectangle partition has at least as many parts as any fooling set.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Rectangle

variable {X Y α : Type*}

/-- A subset of `X × Y` is a rectangle if it factors as `A ×ˢ B`. -/
def IsRectangle (S : Set (X × Y)) : Prop :=
  ∃ A : Set X, ∃ B : Set Y, S = A ×ˢ B

/-- Characterization of rectangles by the cross property:
if `(x,y)` and `(x',y')` are in `R`, then the mixed pairs are also in `R`. -/
theorem IsRectangle_iff (R : Set (X × Y)) :
    IsRectangle R ↔ ∀ x x' y y', (x, y) ∈ R → (x', y') ∈ R → (x', y) ∈ R ∧ (x, y') ∈ R := by
  constructor
  · rintro ⟨A, B, rfl⟩ x x' y y' ⟨hx, hy⟩ ⟨hx', hy'⟩
    exact ⟨⟨hx', hy⟩, ⟨hx, hy'⟩⟩
  · intro h
    refine ⟨Prod.fst '' R, Prod.snd '' R, ?_⟩
    ext ⟨x, y⟩
    simp only [Set.mem_prod, Set.mem_image, Prod.exists]
    constructor
    · intro hxy
      exact ⟨⟨x, y, hxy, rfl⟩, ⟨x, y, hxy, rfl⟩⟩
    · rintro ⟨⟨x', y', hx'y', rfl⟩, ⟨x'', y'', hx''y'', rfl⟩⟩
      exact (h _ _ _ _ hx'y' hx''y'').2

/-- A set is monochromatic for `g` if `g` is constant on that set. -/
def IsMonochromatic (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ x x' y y', (x, y) ∈ S → (x', y') ∈ S → g x y = g x' y'

/-- A set `S ⊆ X × Y` is a fooling set for `g` if every monochromatic
rectangle with respect to `g` contains at most one point of `S`. -/
def IsFoolingSet (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ R : Set (X × Y), IsRectangle R → IsMonochromatic R g →
    (S ∩ R).Subsingleton

/-- A set of sets is a monochromatic rectangle partition of `X × Y`
with respect to `g` if every member is a rectangle, every member is
monochromatic for `g`, the members cover `X × Y`, and distinct
members are disjoint. -/
def IsMonoPartition
    (Part : Set (Set (X × Y))) (g : X → Y → α) : Prop :=
  (∀ R ∈ Part, IsRectangle R) ∧
  (∀ R ∈ Part, IsMonochromatic R g) ∧
  ⋃₀ Part = Set.univ ∧
  (∀ R S, R ∈ Part → S ∈ Part → R ≠ S → Disjoint R S)

variable {Part : Set (Set (X × Y))} {g : X → Y → α}

/-- Every point is in some member of a monochromatic rectangle partition. -/
theorem monoPartition_point_mem (h : IsMonoPartition Part g)
    (p : X × Y) : ∃ R ∈ Part, p ∈ R := by
  have := h.2.2.1 ▸ Set.mem_univ p
  exact Set.mem_sUnion.mp this

/-- If a point is in two parts of a monochromatic rectangle partition,
the parts must be equal. -/
theorem monoPartition_part_unique (h : IsMonoPartition Part g)
    {R S : Set (X × Y)} (hR : R ∈ Part) (hS : S ∈ Part)
    {p : X × Y} (hp1 : p ∈ R) (hp2 : p ∈ S) : R = S := by
  by_contra hne
  exact Set.disjoint_left.mp (h.2.2.2 R S hR hS hne) hp1 hp2

/-- In a monochromatic rectangle partition, if `(x,y)` and `(x',y')`
are in the same part, then so are `(x',y)` and `(x,y')`. -/
theorem monoPartition_cross_mem (h : IsMonoPartition Part g)
    {R : Set (X × Y)} (hR : R ∈ Part)
    {x x' : X} {y y' : Y}
    (hxy : (x, y) ∈ R) (hx'y' : (x', y') ∈ R) :
    (x', y) ∈ R ∧ (x, y') ∈ R :=
  (IsRectangle_iff R).mp (h.1 R hR) x x' y y' hxy hx'y'

/-- In a monochromatic rectangle partition, any two points in the
same part have equal function values. -/
theorem monoPartition_values_eq (h : IsMonoPartition Part g)
    {R : Set (X × Y)} (hR : R ∈ Part)
    {x x' : X} {y y' : Y}
    (hxy : (x, y) ∈ R) (hx'y' : (x', y') ∈ R) :
    g x y = g x' y' :=
  h.2.1 R hR x x' y y' hxy hx'y'

open Classical in
/-- Any monochromatic rectangle partition has at least as many parts as
any fooling set for the same function. -/
theorem foolingSet_encard_le_of_monoPartition
    {S : Set (X × Y)} (hS : IsFoolingSet S g) (hPart : IsMonoPartition Part g) :
    S.encard ≤ Part.encard := by
  classical
  choose rect hrect_mem hrect_in using fun p : X × Y => monoPartition_point_mem hPart p
  have hmaps : ∀ p ∈ S, rect p ∈ Part := fun p _ => hrect_mem p
  have hinj : Set.InjOn rect S := by
    intro p hp q hq hpq
    have hsub :=
      hS (rect p) (hPart.1 _ (hrect_mem p)) (hPart.2.1 _ (hrect_mem p))
    exact hsub ⟨hp, hrect_in p⟩ ⟨hq, by simpa [hpq] using hrect_in q⟩
  exact Set.encard_le_encard_of_injOn hmaps hinj

/-- Any finite monochromatic rectangle partition has at least as many parts as
any fooling set for the same function. -/
theorem foolingSet_ncard_le_of_monoPartition
    {S : Set (X × Y)} (hS : IsFoolingSet S g) (hPart : IsMonoPartition Part g)
    (hfin : Part.Finite) :
    Set.ncard S ≤ Set.ncard Part := by
  have henc := foolingSet_encard_le_of_monoPartition hS hPart
  have hSfin : S.Finite := hfin.finite_of_encard_le henc
  simpa [Set.ncard] using ENat.toNat_le_toNat henc hfin.encard_lt_top.ne

end Rectangle

end CommunicationComplexity
