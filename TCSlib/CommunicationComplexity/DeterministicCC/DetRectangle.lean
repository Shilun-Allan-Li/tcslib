/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.Rectangle
import TCSlib.CommunicationComplexity.DeterministicCC.Subprotocol
import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Protocol Leaf-Rectangle Decomposition

## Main results

- `Deterministic.Protocol.rectangle_partition`: any protocol computing `g` induces a monochromatic rectangle partition of the input space with at most `2^c` parts
- `Deterministic.Protocol.leafRectangles_isMonoPartition`: the leaf rectangles of a protocol form a monochromatic rectangle partition
- `Deterministic.clog_ncard_le_communicationComplexity`: fooling-set lower bound — `⌈log₂ |S|⌉ ≤ CC(g)` for every fooling set `S`
- `Deterministic.foolingSet_ncard_le_pow_of_communicationComplexity_le`: if `CC(g) ≤ n` then every fooling set has size at most `2^n`

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

/-- Swap the two coordinates in a protocol leaf rectangle. -/
def swapInputSet (R : Set (X × Y)) : Set (Y × X) :=
  {yx | (yx.2, yx.1) ∈ R}

@[simp]
theorem mem_swapInputSet (R : Set (X × Y)) (yx : Y × X) :
    yx ∈ swapInputSet R ↔ (yx.2, yx.1) ∈ R :=
  Iff.rfl

@[simp]
theorem swapInputSet_swapInputSet (R : Set (X × Y)) :
    swapInputSet (swapInputSet R) = R := by
  ext xy
  rfl

/-- Pull a protocol input set back along maps on Alice's and Bob's inputs. -/
def preimageInputSet {X' Y' : Type*} (fX : X' → X) (fY : Y' → Y) (R : Set (X × Y)) :
    Set (X' × Y') :=
  {xy | (fX xy.1, fY xy.2) ∈ R}

@[simp]
theorem mem_preimageInputSet {X' Y' : Type*} (fX : X' → X) (fY : Y' → Y) (R : Set (X × Y))
    (xy : X' × Y') :
    xy ∈ preimageInputSet fX fY R ↔ (fX xy.1, fY xy.2) ∈ R :=
  Iff.rfl

-- Internal: leaf rectangles relative to a constraint A × B.
private def leafRectanglesAux (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set (Set (X × Y)) :=
  match p with
  | output _  => {A ×ˢ B}
  | alice f P => leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                 leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B
  | bob   f P => leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                 leafRectanglesAux (P true)  A (B ∩ {y | f y = true})

/-- The set of rectangles induced by protocol leaves over all inputs `X × Y`. -/
def leafRectangles (p : Protocol X Y α) : Set (Set (X × Y)) :=
  leafRectanglesAux p Set.univ Set.univ

private theorem swapInputSet_mem_leafRectanglesAux_swap
    (p : Protocol X Y α) (A : Set X) (B : Set Y) {R : Set (X × Y)}
    (hR : R ∈ leafRectanglesAux p A B) :
    swapInputSet R ∈ leafRectanglesAux p.swap B A := by
  induction p generalizing A B with
  | output val =>
      simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR ⊢
      subst hR
      ext yx
      simp [swapInputSet, and_comm]
  | alice f P ih =>
      simp only [leafRectanglesAux, Set.mem_union] at hR ⊢
      rcases hR with hR | hR
      · exact Or.inl (ih false (A ∩ {x | f x = false}) B hR)
      · exact Or.inr (ih true (A ∩ {x | f x = true}) B hR)
  | bob f P ih =>
      simp only [leafRectanglesAux, Set.mem_union] at hR ⊢
      rcases hR with hR | hR
      · exact Or.inl (ih false A (B ∩ {y | f y = false}) hR)
      · exact Or.inr (ih true A (B ∩ {y | f y = true}) hR)

/-- Swapping Alice and Bob sends protocol leaf rectangles to protocol leaf rectangles. -/
theorem swapInputSet_mem_leafRectangles_swap
    (p : Protocol X Y α) {R : Set (X × Y)}
    (hR : R ∈ p.leafRectangles) :
    swapInputSet R ∈ p.swap.leafRectangles :=
  swapInputSet_mem_leafRectanglesAux_swap p Set.univ Set.univ hR

private theorem preimageInputSet_mem_leafRectanglesAux_comap
    {X' Y' : Type*}
    (p : Protocol X Y α) (A : Set X) (B : Set Y) {R : Set (X × Y)}
    (fX : X' → X) (fY : Y' → Y)
    (hR : R ∈ leafRectanglesAux p A B) :
    preimageInputSet fX fY R ∈
      leafRectanglesAux (p.comap fX fY) (fX ⁻¹' A) (fY ⁻¹' B) := by
  induction p generalizing A B with
  | output val =>
      simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR ⊢
      subst hR
      ext xy
      simp [preimageInputSet]
  | alice f P ih =>
      simp only [leafRectanglesAux, Set.mem_union] at hR ⊢
      rcases hR with hR | hR
      · refine Or.inl ?_
        exact ih false (A ∩ {x | f x = false}) B hR
      · refine Or.inr ?_
        exact ih true (A ∩ {x | f x = true}) B hR
  | bob f P ih =>
      simp only [leafRectanglesAux, Set.mem_union] at hR ⊢
      rcases hR with hR | hR
      · refine Or.inl ?_
        exact ih false A (B ∩ {y | f y = false}) hR
      · refine Or.inr ?_
        exact ih true A (B ∩ {y | f y = true}) hR

/-- Pulling back along `Protocol.comap` sends protocol leaf rectangles to protocol leaf
rectangles. -/
theorem preimageInputSet_mem_leafRectangles_comap
    {X' Y' : Type*}
    (p : Protocol X Y α) {R : Set (X × Y)}
    (fX : X' → X) (fY : Y' → Y)
    (hR : R ∈ p.leafRectangles) :
    preimageInputSet fX fY R ∈ (p.comap fX fY).leafRectangles := by
  simpa [leafRectangles] using
    preimageInputSet_mem_leafRectanglesAux_comap p Set.univ Set.univ fX fY hR

private lemma aux_isRectangle (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : Rectangle.IsRectangle R := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    exact ⟨A, B, hR⟩
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h

/-- Every protocol leaf-rectangle is a genuine rectangle. -/
lemma leafRectangles_isRectangle (p : Protocol X Y α)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsRectangle R :=
  aux_isRectangle p Set.univ Set.univ R hR

private lemma aux_subset (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : R ⊆ A ×ˢ B := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    subst hR; exact le_refl _
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;>
      exact (ih _ _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx.1, hy⟩)
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;>
      exact (ih _ _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx, hy.1⟩)

private lemma aux_cover (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    A ×ˢ B ⊆ ⋃₀ leafRectanglesAux p A B := by
  induction p generalizing A B with
  | output _ =>
    intro xy hxy
    exact Set.mem_sUnion.mpr ⟨_, Set.mem_singleton _, hxy⟩
  | alice f P ih =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f x with
    | false => exact Set.mem_union_left  _ (ih false _ _ ⟨⟨hx, hf⟩, hy⟩)
    | true  => exact Set.mem_union_right _ (ih true  _ _ ⟨⟨hx, hf⟩, hy⟩)
  | bob f P ih =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f y with
    | false => exact Set.mem_union_left  _ (ih false _ _ ⟨hx, ⟨hy, hf⟩⟩)
    | true  => exact Set.mem_union_right _ (ih true  _ _ ⟨hx, ⟨hy, hf⟩⟩)

private lemma aux_disjoint (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R S : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) (hS : S ∈ leafRectanglesAux p A B)
    (hne : R ≠ S) : Disjoint R S := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR hS
    exact absurd (hR.trans hS.symm) hne
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P false) _ _ R hR hxyR).1.2
      have h2 := (aux_subset (P true)  _ _ S hS hxyS).1.2
      simp_all
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P true)  _ _ R hR hxyR).1.2
      have h2 := (aux_subset (P false) _ _ S hS hxyS).1.2
      simp_all
    · exact ih true _ _ hR hS
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P false) _ _ R hR hxyR).2.2
      have h2 := (aux_subset (P true)  _ _ S hS hxyS).2.2
      simp_all
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P true)  _ _ R hR hxyR).2.2
      have h2 := (aux_subset (P false) _ _ S hS hxyS).2.2
      simp_all
    · exact ih true _ _ hR hS

/-- The leaf rectangles of a protocol cover the whole input space. -/
lemma leafRectangles_cover (p : Protocol X Y α) :
    ⋃₀ leafRectangles p = Set.univ :=
  Set.eq_univ_of_univ_subset (by simpa using aux_cover p Set.univ Set.univ)

/-- Distinct protocol leaf rectangles are disjoint. -/
lemma leafRectangles_disjoint (p : Protocol X Y α)
    (R S : Set (X × Y)) (hR : R ∈ leafRectangles p) (hS : S ∈ leafRectangles p)
    (hne : R ≠ S) : Disjoint R S :=
  aux_disjoint p Set.univ Set.univ R S hR hS hne

private lemma aux_mono (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B)
    (x x' : X) (y y' : Y) (hxy : (x, y) ∈ R) (hxy' : (x', y') ∈ R) :
    p.run x y = p.run x' y' := by
  induction p generalizing A B with
  | output v => rfl
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with hR | hR
    · have hfx  : f x  = false := (aux_subset (P false) _ _ R hR hxy).1.2
      have hfx' : f x' = false := (aux_subset (P false) _ _ R hR hxy').1.2
      simp only [run, hfx, hfx']
      exact ih false _ _ hR
    · have hfx  : f x  = true := (aux_subset (P true) _ _ R hR hxy).1.2
      have hfx' : f x' = true := (aux_subset (P true) _ _ R hR hxy').1.2
      simp only [run, hfx, hfx']
      exact ih true _ _ hR
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with hR | hR
    · have hfy  : f y  = false := (aux_subset (P false) _ _ R hR hxy).2.2
      have hfy' : f y' = false := (aux_subset (P false) _ _ R hR hxy').2.2
      simp only [run, hfy, hfy']
      exact ih false _ _ hR
    · have hfy  : f y  = true := (aux_subset (P true) _ _ R hR hxy).2.2
      have hfy' : f y' = true := (aux_subset (P true) _ _ R hR hxy').2.2
      simp only [run, hfy, hfy']
      exact ih true _ _ hR

lemma leafRectangles_mono (p : Protocol X Y α)
    (g : X → Y → α) (h_comp : Computes p g)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsMonochromatic R g := by
  intro x x' y y' hxy hxy'
  have := aux_mono p Set.univ Set.univ R hR x x' y y' hxy hxy'
  simp only [Computes, funext_iff] at h_comp
  rw [← h_comp x y, ← h_comp x' y']; exact this

private lemma aux_card (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set.ncard (leafRectanglesAux p A B) ≤ 2 ^ p.complexity := by
  induction p generalizing A B with
  | output _ =>
    simp [leafRectanglesAux, complexity]
  | alice f P ih =>
    simp only [leafRectanglesAux, complexity]
    calc Set.ncard (leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                    leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B)
        ≤ Set.ncard (leafRectanglesAux (P false) (A ∩ {x | f x = false}) B) +
          Set.ncard (leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B) :=
            Set.ncard_union_le _ _
      _ ≤ 2 ^ (P false).complexity + 2 ^ (P true).complexity := by
            exact Nat.add_le_add (ih false _ _) (ih true _ _)
      _ ≤ 2 ^ max (P false).complexity (P true).complexity +
          2 ^ max (P false).complexity (P true).complexity :=
            Nat.add_le_add
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
      _ = 2 ^ (1 + max (P false).complexity (P true).complexity) := by ring
  | bob f P ih =>
    simp only [leafRectanglesAux, complexity]
    calc Set.ncard (leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                    leafRectanglesAux (P true)  A (B ∩ {y | f y = true}))
        ≤ Set.ncard (leafRectanglesAux (P false) A (B ∩ {y | f y = false})) +
          Set.ncard (leafRectanglesAux (P true)  A (B ∩ {y | f y = true})) :=
            Set.ncard_union_le _ _
      _ ≤ 2 ^ (P false).complexity + 2 ^ (P true).complexity :=
            Nat.add_le_add (ih false _ _) (ih true _ _)
      _ ≤ 2 ^ max (P false).complexity (P true).complexity +
          2 ^ max (P false).complexity (P true).complexity :=
            Nat.add_le_add
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
      _ = 2 ^ (1 + max (P false).complexity (P true).complexity) := by ring

private lemma aux_finite (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    (leafRectanglesAux p A B).Finite := by
  induction p generalizing A B with
  | output _ =>
    simp [leafRectanglesAux]
  | alice f P ih =>
    simp only [leafRectanglesAux]
    exact (ih false _ _).union (ih true _ _)
  | bob f P ih =>
    simp only [leafRectanglesAux]
    exact (ih false _ _).union (ih true _ _)

lemma leafRectangles_card (p : Protocol X Y α) :
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  aux_card p Set.univ Set.univ

/-- The set of protocol leaf rectangles is finite. -/
lemma leafRectangles_finite (p : Protocol X Y α) :
    (leafRectangles p).Finite :=
  aux_finite p Set.univ Set.univ

/-- The leaf rectangles of a protocol computing `g` form a
monochromatic rectangle partition. -/
theorem leafRectangles_isMonoPartition
    (p : Protocol X Y α) (g : X → Y → α)
    (h_comp : Computes p g) :
    Rectangle.IsMonoPartition (leafRectangles p) g :=
  ⟨fun R hR => leafRectangles_isRectangle p R hR,
   fun R hR => leafRectangles_mono p g h_comp R hR,
   leafRectangles_cover p,
   fun R S hR hS hne =>
     leafRectangles_disjoint p R S hR hS hne⟩

/-- Theorem 1.6: if π computes g, then X × Y is partitioned
into at most 2^c monochromatic rectangles with respect to g. -/
theorem rectangle_partition
    (p : Protocol X Y α) (g : X → Y → α)
    (h_comp : Computes p g) :
    Rectangle.IsMonoPartition (leafRectangles p) g ∧
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  ⟨leafRectangles_isMonoPartition p g h_comp,
   leafRectangles_card p⟩

/-- The input pairs that reach a fixed subprotocol path form a rectangle. -/
theorem reachesPath_isRectangle {s p : Protocol X Y α} (hsp : SubprotocolPath s p) :
    Rectangle.IsRectangle {xy : X × Y | reachesPath hsp xy.1 xy.2} := by
  refine ⟨reachXPath hsp, reachYPath hsp, ?_⟩
  ext xy
  rcases xy with ⟨x, y⟩
  simp [reachesPath, Set.mem_prod]

/-- The input pairs that reach a chosen subprotocol witness form a rectangle. -/
theorem reaches_isRectangle {s p : Protocol X Y α} (hsp : IsSubprotocol s p) :
    Rectangle.IsRectangle {xy : X × Y | reaches hsp xy.1 xy.2} := by
  simpa [reaches, reachX, reachY] using reachesPath_isRectangle (choosePath hsp)

end Deterministic.Protocol

namespace Deterministic

variable {X Y α : Type*}

/-- If `deterministic_communication_complexity g ≤ n`, then there is a monochromatic
rectangle partition of `X × Y` with at most `2^n` rectangles. -/
theorem mono_partition_of_communicationComplexity_le
    (g : X → Y → α) (n : ℕ)
    (h : communicationComplexity g ≤ n) :
    ∃ Part : Set (Set (X × Y)),
      Rectangle.IsMonoPartition Part g ∧
      Set.ncard Part ≤ 2 ^ n := by
  obtain ⟨p, hp, hc⟩ := (communicationComplexity_le_iff g n).mp h
  exact ⟨Protocol.leafRectangles p,
    Protocol.leafRectangles_isMonoPartition p g hp,
    (Protocol.leafRectangles_card p).trans
      (Nat.pow_le_pow_right (by omega) hc)⟩

/-- Rectangle lower-bound method: to prove `CC(g) ≥ n + 1`, it suffices to show
every monochromatic rectangle partition of `g` has more than `2^n` parts. -/
theorem le_communicationComplexity_of_forall_lt_ncard
    (g : X → Y → α) (n : ℕ)
    (h : ∀ Part : Set (Set (X × Y)),
      Rectangle.IsMonoPartition Part g →
      2 ^ n < Set.ncard Part) :
    (n + 1 : ℕ) ≤ communicationComplexity g := by
  rw [le_communicationComplexity_iff]
  intro p hp
  have hle : communicationComplexity g ≤
      p.complexity :=
    (communicationComplexity_le_iff g p.complexity).mpr ⟨p, hp, le_refl _⟩
  obtain ⟨Part, hPart, hCard⟩ :=
    mono_partition_of_communicationComplexity_le g p.complexity hle
  have hsuff := h Part hPart
  by_contra hlt; push_neg at hlt
  have : 2 ^ p.complexity ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

open Rectangle in
/-- If the deterministic communication complexity of `g` is at most `n`,
then every fooling set for `g` has size at most `2^n`. -/
theorem foolingSet_ncard_le_pow_of_communicationComplexity_le
    (g : X → Y → α) (S : Set (X × Y)) (n : ℕ)
    (hS : Rectangle.IsFoolingSet S g)
    (h : communicationComplexity g ≤ n) :
    Set.ncard S ≤ 2 ^ n := by
  obtain ⟨p, hp, hc⟩ := (communicationComplexity_le_iff g n).mp h
  let Part := Protocol.leafRectangles p
  have hPart : Rectangle.IsMonoPartition Part g :=
    Protocol.leafRectangles_isMonoPartition p g hp
  have hCard : Set.ncard Part ≤ 2 ^ n :=
    (Protocol.leafRectangles_card p).trans (Nat.pow_le_pow_right (by omega) hc)
  exact (Rectangle.foolingSet_ncard_le_of_monoPartition hS hPart
    (Protocol.leafRectangles_finite p)).trans hCard

/-- Fooling-set lower bound: the deterministic communication complexity
of `g` is at least `⌈log₂ |S|⌉` for every fooling set `S` of `g`. -/
theorem clog_ncard_le_communicationComplexity
    (g : X → Y → α) (S : Set (X × Y))
    (hS : Rectangle.IsFoolingSet S g) :
    (Nat.clog 2 (Set.ncard S) : ENat) ≤ communicationComplexity g := by
  match h : communicationComplexity g with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    exact_mod_cast (Nat.clog_le_iff_le_pow (by norm_num)).mpr
      (foolingSet_ncard_le_pow_of_communicationComplexity_le g S n hS (le_of_eq h))

end Deterministic

end CommunicationComplexity
