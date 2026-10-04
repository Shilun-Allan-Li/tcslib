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

Combinatorial rectangles `A × B ⊆ X × Y`, monochromatic rectangles, fooling sets and
monochromatic rectangle partitions, together with the fooling-set counting bound: a
monochromatic rectangle partition has at least as many parts as any fooling set. The
connection to protocols (every protocol partitions the inputs into monochromatic rectangles)
is made in `DetRectangle.lean`; this file is purely set-theoretic.

## Main definitions

- `Rectangle.IsRectangle`: a subset of `X × Y` is a rectangle if it factors as `A ×ˢ B`
- `Rectangle.IsMonochromatic`: a set is monochromatic for `g` if `g` is constant on it
- `Rectangle.IsFoolingSet`: a fooling set for `g` meets every monochromatic rectangle in at
  most one point
- `Rectangle.IsMonoPartition`: a monochromatic rectangle partition covers `X × Y` by
  pairwise disjoint monochromatic rectangles

## Main results

- `Rectangle.IsRectangle_iff`: a set is a rectangle iff it is closed under mixing the
  coordinates of any two of its points
- `Rectangle.foolingSet_encard_le_of_monoPartition`,
  `Rectangle.foolingSet_ncard_le_of_monoPartition`: a monochromatic rectangle partition has
  at least as many parts as any fooling set (extended and finite cardinalities)

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*,
  Cambridge University Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Rectangle

variable {X Y α : Type*}

/-- A subset of `X × Y` is a (combinatorial) rectangle if it is a product `A ×ˢ B` of a set
of `X`-inputs and a set of `Y`-inputs. [RY20, Ch. 1, 'Rectangles'] /
[Rou16, §4.2.4 Definition (rectangle)]. -/
def IsRectangle (S : Set (X × Y)) : Prop :=
  ∃ A : Set X, ∃ B : Set Y, S = A ×ˢ B

/-- A set `R ⊆ X × Y` is a rectangle if and only if it has the cross property: whenever
`(x, y)` and `(x', y')` lie in `R`, so do the mixed pairs `(x', y)` and `(x, y')`.
[RY20, Lemma 1.5]. -/
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

/-- A set `S ⊆ X × Y` is monochromatic for `g` if `g` takes the same value at any two points
of `S`. [RY20, Ch. 1, Definition (monochromatic)]. -/
def IsMonochromatic (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ x x' y y', (x, y) ∈ S → (x', y') ∈ S → g x y = g x' y'

/-- A set `S ⊆ X × Y` is a fooling set for `g` if every monochromatic
rectangle with respect to `g` contains at most one point of `S`.
[Rou16, §4.2.5 Definition (fooling set)]. Deviation: Rou16 define a fooling set by the two
conditions "`g` is constant on `S`" and "for distinct points of `S`, one of the two mixed
pairs has a different `g`-value"; the definition here is the consequence those conditions
are used for (every monochromatic rectangle meets `S` in at most one point), which is all
the counting bound needs. -/
def IsFoolingSet (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ R : Set (X × Y), IsRectangle R → IsMonochromatic R g →
    (S ∩ R).Subsingleton

/-- A set of sets is a monochromatic rectangle partition of `X × Y`
with respect to `g` if every member is a rectangle, every member is
monochromatic for `g`, the members cover `X × Y`, and distinct
members are disjoint. [RY20, Thm 1.7] (the notion of a partition of `X × Y` into
monochromatic rectangles). -/
def IsMonoPartition
    (Part : Set (Set (X × Y))) (g : X → Y → α) : Prop :=
  (∀ R ∈ Part, IsRectangle R) ∧
  (∀ R ∈ Part, IsMonochromatic R g) ∧
  ⋃₀ Part = Set.univ ∧
  (∀ R S, R ∈ Part → S ∈ Part → R ≠ S → Disjoint R S)

variable {Part : Set (Set (X × Y))} {g : X → Y → α}

/-- Every point of `X × Y` lies in some member of a monochromatic rectangle partition. -/
theorem monoPartition_point_mem (h : IsMonoPartition Part g)
    (p : X × Y) : ∃ R ∈ Part, p ∈ R := by
  have := h.2.2.1 ▸ Set.mem_univ p
  exact Set.mem_sUnion.mp this

/-- If a point lies in two members of a monochromatic rectangle partition,
the two members are equal. -/
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
any fooling set for the same function (as extended cardinals, so no finiteness is
assumed). [Rou16, Cor 4.7] (its proof: each fooling-set element needs its own monochromatic
rectangle). Deviation: Rou16 conclude `D(g) ≥ log₂ |F|`; the statement here is the
combinatorial core comparing `|F|` with the size of an arbitrary monochromatic rectangle
partition, which yields Rou16's form once combined with the `2^c`-part partition of
[RY20, Thm 1.7]. The proof chooses, for each point, a member containing it; on the fooling
set this choice is injective because a member containing two fooling-set points would be a
monochromatic rectangle meeting the fooling set twice. -/
theorem foolingSet_encard_le_of_monoPartition
    {S : Set (X × Y)} (hS : IsFoolingSet S g) (hPart : IsMonoPartition Part g) :
    S.encard ≤ Part.encard := by
  choose rect hrect_mem hrect_in using fun p : X × Y => monoPartition_point_mem hPart p
  have hmaps : ∀ p ∈ S, rect p ∈ Part := fun p _ => hrect_mem p
  have hinj : Set.InjOn rect S := by
    intro p hp q hq hpq
    have hsub :=
      hS (rect p) (hPart.1 _ (hrect_mem p)) (hPart.2.1 _ (hrect_mem p))
    exact hsub ⟨hp, hrect_in p⟩ ⟨hq, by simpa [hpq] using hrect_in q⟩
  exact Set.encard_le_encard_of_injOn hmaps hinj

/-- Any finite monochromatic rectangle partition has at least as many parts as
any fooling set for the same function (as natural-number cardinalities; the fooling set is
then finite too). [Rou16, Cor 4.7] (its proof: each fooling-set element needs its own
monochromatic rectangle); see `foolingSet_encard_le_of_monoPartition` for the deviation. -/
theorem foolingSet_ncard_le_of_monoPartition
    {S : Set (X × Y)} (hS : IsFoolingSet S g) (hPart : IsMonoPartition Part g)
    (hfin : Part.Finite) :
    Set.ncard S ≤ Set.ncard Part := by
  have henc := foolingSet_encard_le_of_monoPartition hS hPart
  have hSfin : S.Finite := hfin.finite_of_encard_le henc
  simpa [Set.ncard] using ENat.toNat_le_toNat henc hfin.encard_lt_top.ne

end Rectangle

end CommunicationComplexity
