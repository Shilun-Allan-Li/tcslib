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

The leaves of a deterministic protocol partition the input space `X × Y` into combinatorial
rectangles, one per leaf, and when the protocol computes `g` each of these rectangles is
monochromatic for `g` [RY20, Lemma 1.6]. This file constructs the set of leaf rectangles of a
protocol, proves that it is a monochromatic rectangle partition with at most `2 ^ c` parts
for a protocol of complexity `c`, and derives the rectangle and fooling-set lower bounds on
deterministic communication complexity [RY20, Thm 1.7], [Rou16, Cor 4.7].

## Main definitions

- `Deterministic.Protocol.leafRectangles`: the set of leaf rectangles of a protocol, i.e. the
  sets of inputs reaching each leaf.
- `Deterministic.Protocol.swapInputSet`, `Deterministic.Protocol.preimageInputSet`: transport
  of input sets along `Protocol.swap` and `Protocol.comap`.

## Main results

- `Deterministic.Protocol.rectangle_partition`: any protocol of complexity `c` computing `g`
  induces a monochromatic rectangle partition of the input space with at most `2 ^ c` parts.
- `Deterministic.Protocol.leafRectangles_isMonoPartition`: the leaf rectangles of a protocol
  computing `g` form a monochromatic rectangle partition.
- `Deterministic.Protocol.leafRectangles_card`: a protocol of complexity `c` has at most
  `2 ^ c` leaf rectangles.
- `Deterministic.mono_partition_of_communicationComplexity_le`,
  `Deterministic.le_communicationComplexity_of_forall_lt_ncard`: the rectangle lower-bound
  method.
- `Deterministic.clog_ncard_le_communicationComplexity`: fooling-set lower bound —
  `⌈log₂ |S|⌉ ≤ CC(g)` for every fooling set `S`.
- `Deterministic.foolingSet_ncard_le_pow_of_communicationComplexity_le`: if `CC(g) ≤ n` then
  every fooling set has size at most `2 ^ n`.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

/-- The image of a set of inputs `R ⊆ X × Y` under the coordinate swap: the set of pairs
`(y, x)` with `(x, y) ∈ R`. Used to transport leaf rectangles along `Protocol.swap`. -/
def swapInputSet (R : Set (X × Y)) : Set (Y × X) :=
  {yx | (yx.2, yx.1) ∈ R}

/-- A pair `(y, x)` lies in the swapped set exactly when `(x, y)` lies in the original set. -/
@[simp]
theorem mem_swapInputSet (R : Set (X × Y)) (yx : Y × X) :
    yx ∈ swapInputSet R ↔ (yx.2, yx.1) ∈ R :=
  Iff.rfl

/-- Swapping the coordinates of a set of inputs twice returns the original set. -/
@[simp]
theorem swapInputSet_swapInputSet (R : Set (X × Y)) :
    swapInputSet (swapInputSet R) = R := by
  ext xy
  rfl

/-- The preimage of a set of inputs `R ⊆ X × Y` under the product map `fX × fY`: the set of
pairs `(x', y')` with `(fX x', fY y') ∈ R`. Used to transport leaf rectangles along
`Protocol.comap`. -/
def preimageInputSet {X' Y' : Type*} (fX : X' → X) (fY : Y' → Y) (R : Set (X × Y)) :
    Set (X' × Y') :=
  {xy | (fX xy.1, fY xy.2) ∈ R}

/-- A pair `(x', y')` lies in the pulled-back set exactly when `(fX x', fY y')` lies in the
original set. -/
@[simp]
theorem mem_preimageInputSet {X' Y' : Type*} (fX : X' → X) (fY : Y' → Y) (R : Set (X × Y))
    (xy : X' × Y') :
    xy ∈ preimageInputSet fX fY R ↔ (fX xy.1, fY xy.2) ∈ R :=
  Iff.rfl

/-- The leaf rectangles of a protocol relative to a constraint rectangle `A ×ˢ B`, i.e. the
sets of inputs in `A ×ˢ B` reaching each leaf: a terminal protocol contributes `A ×ˢ B`
itself, an Alice node with message function `f` the leaf rectangles of the child reached on
bit `b` relative to `(A ∩ {x | f x = b}) ×ˢ B` for both `b`, and a Bob node likewise with the
constraint on `B`. `leafRectangles` is the case `A = B = univ`. -/
private def leafRectanglesAux (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set (Set (X × Y)) :=
  match p with
  | output _  => {A ×ˢ B}
  | alice f P => leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                 leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B
  | bob   f P => leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                 leafRectanglesAux (P true)  A (B ∩ {y | f y = true})

/-- The set of leaf rectangles of a protocol: for each leaf `v`, the set `R_v` of inputs
`(x, y)` on which the protocol reaches `v` [RY20, Lemma 1.6] (the rectangles `R_v` of the
leaves). Deviation: this is a set of subsets of `X × Y` rather than a family indexed by the
leaves, so leaves with identical input sets (for instance two unreachable leaves, both with
empty input set) contribute a single element. -/
def leafRectangles (p : Protocol X Y α) : Set (Set (X × Y)) :=
  leafRectanglesAux p Set.univ Set.univ

/-- Relative form of `swapInputSet_mem_leafRectangles_swap`: swapping a leaf rectangle of `p`
relative to `A ×ˢ B` gives a leaf rectangle of `p.swap` relative to `B ×ˢ A`. Proved by
induction on `p`, following the same child of the split. -/
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

/-- The coordinate swap of a leaf rectangle of `p` is a leaf rectangle of the swapped
protocol `p.swap`. -/
theorem swapInputSet_mem_leafRectangles_swap
    (p : Protocol X Y α) {R : Set (X × Y)}
    (hR : R ∈ p.leafRectangles) :
    swapInputSet R ∈ p.swap.leafRectangles :=
  swapInputSet_mem_leafRectanglesAux_swap p Set.univ Set.univ hR

/-- Relative form of `preimageInputSet_mem_leafRectangles_comap`: the preimage under
`fX × fY` of a leaf rectangle of `p` relative to `A ×ˢ B` is a leaf rectangle of
`p.comap fX fY` relative to `(fX ⁻¹' A) ×ˢ (fY ⁻¹' B)`. Proved by induction on `p`,
following the same child of the split.

**Proof sketch.** Induction on `p`, generalizing `A` and `B`. In the `output` case the only
leaf rectangle relative to `A ×ˢ B` is `A ×ˢ B` itself, and its preimage is
`(fX ⁻¹' A) ×ˢ (fY ⁻¹' B)` by extensionality. In the `alice f P` case the leaf rectangles are
the union over the two children, the child for bit `b` being taken relative to
`(A ∩ {f = b}) ×ˢ B`; since `p.comap fX fY` splits on `f ∘ fX` and
`fX ⁻¹' (A ∩ {f = b})` is definitionally `(fX ⁻¹' A) ∩ {f ∘ fX = b}`, the induction
hypothesis for the same child closes the goal. The `bob` case is symmetric in `B`, `fY`. -/
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

/-- The preimage under `fX × fY` of a leaf rectangle of `p` is a leaf rectangle of the
pulled-back protocol `p.comap fX fY`. -/
theorem preimageInputSet_mem_leafRectangles_comap
    {X' Y' : Type*}
    (p : Protocol X Y α) {R : Set (X × Y)}
    (fX : X' → X) (fY : Y' → Y)
    (hR : R ∈ p.leafRectangles) :
    preimageInputSet fX fY R ∈ (p.comap fX fY).leafRectangles := by
  simpa [leafRectangles] using
    preimageInputSet_mem_leafRectanglesAux_comap p Set.univ Set.univ fX fY hR

/-- Every leaf rectangle of `p` relative to `A ×ˢ B` is a combinatorial rectangle. -/
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

/-- Every leaf rectangle of a protocol is a combinatorial rectangle `A ×ˢ B`
[RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
lemma leafRectangles_isRectangle (p : Protocol X Y α)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsRectangle R :=
  aux_isRectangle p Set.univ Set.univ R hR

/-- Every leaf rectangle of `p` relative to `A ×ˢ B` is contained in `A ×ˢ B`. -/
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

/-- The leaf rectangles of `p` relative to `A ×ˢ B` cover `A ×ˢ B`: an input `(x, y)` lies
in the rectangle of the leaf it reaches, found by following its bits down the tree. -/
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

/-- Shared bit-split step of the `alice` branches: a leaf rectangle of the child reached on
Alice's bit `b` only contains inputs `(x, y)` with `f x = b` (via `aux_subset`). -/
private lemma aux_alice_bit {p : Protocol X Y α} {A : Set X} {B : Set Y} {f : X → Bool}
    {b : Bool} {R : Set (X × Y)} (hR : R ∈ leafRectanglesAux p (A ∩ {x | f x = b}) B)
    {x : X} {y : Y} (hxy : (x, y) ∈ R) : f x = b :=
  (aux_subset p _ _ R hR hxy).1.2

/-- Shared bit-split step of the `bob` branches: a leaf rectangle of the child reached on
Bob's bit `b` only contains inputs `(x, y)` with `f y = b`; mirror of `aux_alice_bit`. -/
private lemma aux_bob_bit {p : Protocol X Y α} {A : Set X} {B : Set Y} {f : Y → Bool}
    {b : Bool} {R : Set (X × Y)} (hR : R ∈ leafRectanglesAux p A (B ∩ {y | f y = b}))
    {x : X} {y : Y} (hxy : (x, y) ∈ R) : f y = b :=
  (aux_subset p _ _ R hR hxy).2.2

/-- Opposite sides of an `alice` split are disjoint: a leaf rectangle of the child reached on
bit `b` and one of the child reached on bit `b' ≠ b` share no input, since no `x` has both
`f x = b` and `f x = b'`. -/
private lemma aux_disjoint_alice_of_ne {p q : Protocol X Y α} {A : Set X} {B : Set Y}
    {f : X → Bool} {b b' : Bool} (hb : b ≠ b') {R S : Set (X × Y)}
    (hR : R ∈ leafRectanglesAux p (A ∩ {x | f x = b}) B)
    (hS : S ∈ leafRectanglesAux q (A ∩ {x | f x = b'}) B) : Disjoint R S := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ hxyR hxyS
  exact hb ((aux_alice_bit hR hxyR).symm.trans (aux_alice_bit hS hxyS))

/-- Opposite sides of a `bob` split are disjoint; mirror of `aux_disjoint_alice_of_ne`. -/
private lemma aux_disjoint_bob_of_ne {p q : Protocol X Y α} {A : Set X} {B : Set Y}
    {f : Y → Bool} {b b' : Bool} (hb : b ≠ b') {R S : Set (X × Y)}
    (hR : R ∈ leafRectanglesAux p A (B ∩ {y | f y = b}))
    (hS : S ∈ leafRectanglesAux q A (B ∩ {y | f y = b'})) : Disjoint R S := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ hxyR hxyS
  exact hb ((aux_bob_bit hR hxyR).symm.trans (aux_bob_bit hS hxyS))

/-- Two distinct leaf rectangles of `p` relative to `A ×ˢ B` are disjoint.

**Proof sketch.** Induction on `p`, generalising the constraint. A terminal protocol has a
single leaf rectangle, contradicting `R ≠ S`. Step 1: at an Alice node each of `R`, `S`
comes from the `false`-child or the `true`-child; if from the same child, apply the induction
hypothesis, and if from opposite children, they are disjoint because an input in both would
have to send both bits (`aux_disjoint_alice_of_ne`). Step 2: a Bob node is the mirror image
with Bob's bit. -/
private lemma aux_disjoint (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R S : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) (hS : S ∈ leafRectanglesAux p A B)
    (hne : R ≠ S) : Disjoint R S := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR hS
    exact absurd (hR.trans hS.symm) hne
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    -- Step 1: same side of the split → induction hypothesis; opposite sides → disjoint.
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · exact aux_disjoint_alice_of_ne Bool.false_ne_true hR hS
    · exact aux_disjoint_alice_of_ne Bool.false_ne_true.symm hR hS
    · exact ih true _ _ hR hS
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    -- Step 2: mirror of Step 1 for Bob's split.
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · exact aux_disjoint_bob_of_ne Bool.false_ne_true hR hS
    · exact aux_disjoint_bob_of_ne Bool.false_ne_true.symm hR hS
    · exact ih true _ _ hR hS

/-- The leaf rectangles of a protocol cover the whole input space `X × Y`
[RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
lemma leafRectangles_cover (p : Protocol X Y α) :
    ⋃₀ leafRectangles p = Set.univ :=
  Set.eq_univ_of_univ_subset (by simpa using aux_cover p Set.univ Set.univ)

/-- Two distinct leaf rectangles of a protocol are disjoint
[RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
lemma leafRectangles_disjoint (p : Protocol X Y α)
    (R S : Set (X × Y)) (hR : R ∈ leafRectangles p) (hS : S ∈ leafRectangles p)
    (hne : R ≠ S) : Disjoint R S :=
  aux_disjoint p Set.univ Set.univ R S hR hS hne

/-- The protocol output is constant on each leaf rectangle of `p` relative to `A ×ˢ B`.

**Proof sketch.** Induction on `p`. A terminal protocol outputs a constant. Step 1: at an
Alice node the rectangle `R` comes from one child, and both inputs in `R` send the bit of
that child (`aux_alice_bit`), so both runs descend into the same child, where the induction
hypothesis applies. Step 2: a Bob node is the mirror image with Bob's bit. -/
private lemma aux_mono (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B)
    (x x' : X) (y y' : Y) (hxy : (x, y) ∈ R) (hxy' : (x', y') ∈ R) :
    p.run x y = p.run x' y' := by
  induction p generalizing A B with
  | output v => rfl
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    -- Step 1: both inputs send the same bit, so the run descends into the same child.
    rcases hR with hR | hR <;>
      simp only [run, aux_alice_bit hR hxy, aux_alice_bit hR hxy'] <;> exact ih _ _ _ hR
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    -- Step 2: mirror of Step 1 for Bob's bit.
    rcases hR with hR | hR <;>
      simp only [run, aux_bob_bit hR hxy, aux_bob_bit hR hxy'] <;> exact ih _ _ _ hR

/-- If `p` computes `g`, then every leaf rectangle of `p` is monochromatic for `g`, i.e. `g`
takes a single value on it [RY20, Lemma 1.6]: two inputs in the same leaf rectangle reach
the same leaf, hence produce the same output. -/
lemma leafRectangles_mono (p : Protocol X Y α)
    (g : X → Y → α) (h_comp : Computes p g)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsMonochromatic R g := by
  intro x x' y y' hxy hxy'
  have := aux_mono p Set.univ Set.univ R hR x x' y y' hxy hxy'
  simp only [Computes, funext_iff] at h_comp
  rw [← h_comp x y, ← h_comp x' y']; exact this

/-- Shared counting step of `aux_card`: if `S₀` has at most `2 ^ c₀` elements and `S₁` at
most `2 ^ c₁`, then `S₀ ∪ S₁` has at most `2 ^ (1 + max c₀ c₁)` elements. The proof is the
union bound, `2 ^ c ≤ 2 ^ max c₀ c₁`, and `2 ^ m + 2 ^ m = 2 ^ (1 + m)`. -/
private lemma aux_card_step {β : Type*} {S₀ S₁ : Set β} {c₀ c₁ : ℕ}
    (h₀ : S₀.ncard ≤ 2 ^ c₀) (h₁ : S₁.ncard ≤ 2 ^ c₁) :
    (S₀ ∪ S₁).ncard ≤ 2 ^ (1 + max c₀ c₁) :=
  calc (S₀ ∪ S₁).ncard
      ≤ S₀.ncard + S₁.ncard := Set.ncard_union_le _ _
    _ ≤ 2 ^ c₀ + 2 ^ c₁ := Nat.add_le_add h₀ h₁
    _ ≤ 2 ^ max c₀ c₁ + 2 ^ max c₀ c₁ :=
        Nat.add_le_add
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    _ = 2 ^ (1 + max c₀ c₁) := by ring

/-- A protocol of complexity `c` has at most `2 ^ c` leaf rectangles relative to any
constraint `A ×ˢ B`.

**Proof sketch.** Induction on `p`. A terminal protocol has one leaf rectangle and
complexity `0`. Step 1: at an Alice node the leaf rectangles are the union of the two
children's, each bounded by the induction hypothesis, and `aux_card_step` gives
`2 ^ c₀ + 2 ^ c₁ ≤ 2 ^ (1 + max c₀ c₁)`, the bound for the node. Step 2: a Bob node is
identical. -/
private lemma aux_card (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set.ncard (leafRectanglesAux p A B) ≤ 2 ^ p.complexity := by
  induction p generalizing A B with
  | output _ =>
    simp [leafRectanglesAux, complexity]
  | alice f P ih =>
    -- Step 1: the two children contribute at most `2^c₀ + 2^c₁ ≤ 2^(1 + max c₀ c₁)`.
    simp only [leafRectanglesAux, complexity]
    exact aux_card_step (ih false _ _) (ih true _ _)
  | bob f P ih =>
    -- Step 2: mirror of Step 1 for Bob's split.
    simp only [leafRectanglesAux, complexity]
    exact aux_card_step (ih false _ _) (ih true _ _)

/-- The set of leaf rectangles of `p` relative to `A ×ˢ B` is finite. -/
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

/-- A protocol of communication complexity `c` has at most `2 ^ c` leaf rectangles
[RY20, Lemma 1.2] (a protocol tree of depth `c` has at most `2 ^ c` leaves). -/
lemma leafRectangles_card (p : Protocol X Y α) :
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  aux_card p Set.univ Set.univ

/-- The set of leaf rectangles of a protocol is finite. -/
lemma leafRectangles_finite (p : Protocol X Y α) :
    (leafRectangles p).Finite :=
  aux_finite p Set.univ Set.univ

/-- If `p` computes `g`, then the leaf rectangles of `p` form a monochromatic rectangle
partition of `X × Y` for `g`: every member is a rectangle, `g` is constant on every member,
the members cover `X × Y`, and distinct members are disjoint
[RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
theorem leafRectangles_isMonoPartition
    (p : Protocol X Y α) (g : X → Y → α)
    (h_comp : Computes p g) :
    Rectangle.IsMonoPartition (leafRectangles p) g :=
  ⟨fun R hR => leafRectangles_isRectangle p R hR,
   fun R hR => leafRectangles_mono p g h_comp R hR,
   leafRectangles_cover p,
   fun R S hR hS hne =>
     leafRectangles_disjoint p R S hR hS hne⟩

/-- If a protocol `p` of communication complexity `c` computes `g`, then its leaf rectangles
partition `X × Y` into monochromatic rectangles for `g`, and there are at most `2 ^ c` of
them [RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
theorem rectangle_partition
    (p : Protocol X Y α) (g : X → Y → α)
    (h_comp : Computes p g) :
    Rectangle.IsMonoPartition (leafRectangles p) g ∧
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  ⟨leafRectangles_isMonoPartition p g h_comp,
   leafRectangles_card p⟩

/-- The set of inputs `(x, y)` on which the protocol follows a fixed path to a subprotocol is
a combinatorial rectangle [RY20, Lemma 1.6] (the rectangle of an internal vertex of the
protocol tree). -/
theorem reachesPath_isRectangle {s p : Protocol X Y α} (hsp : SubprotocolPath s p) :
    Rectangle.IsRectangle {xy : X × Y | reachesPath hsp xy.1 xy.2} := by
  refine ⟨reachXPath hsp, reachYPath hsp, ?_⟩
  ext xy
  rcases xy with ⟨x, y⟩
  simp [reachesPath, Set.mem_prod]

/-- The set of inputs `(x, y)` on which the protocol reaches a subprotocol (along the
classically chosen path `choosePath`) is a combinatorial rectangle [RY20, Lemma 1.6] (the
rectangle of an internal vertex of the protocol tree). -/
theorem reaches_isRectangle {s p : Protocol X Y α} (hsp : IsSubprotocol s p) :
    Rectangle.IsRectangle {xy : X × Y | reaches hsp xy.1 xy.2} := by
  simpa [reaches, reachX, reachY] using reachesPath_isRectangle (choosePath hsp)

end Deterministic.Protocol

namespace Deterministic

variable {X Y α : Type*}

/-- If the deterministic communication complexity of `g` is at most `n`, then there is a
monochromatic rectangle partition of `X × Y` for `g` with at most `2 ^ n` rectangles
[RY20, Thm 1.7]: take the leaf rectangles of a protocol of complexity at most `n`. -/
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

/-- Rectangle lower-bound method: if every monochromatic rectangle partition of `X × Y` for
`g` has more than `2 ^ n` parts, then the deterministic communication complexity of `g` is at
least `n + 1` [RY20, Thm 1.7] (contrapositive) / [Rou16, Thm 4.3]. Deviation: stated with
`2 ^ n` parts and conclusion `n + 1 ≤ D(g)` rather than `log₂ t ≤ D(g)` for a partition
size `t`, avoiding logarithms of naturals. -/
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
/-- If the deterministic communication complexity of `g` is at most `n`, then every fooling
set for `g` has at most `2 ^ n` elements [Rou16, Cor 4.7] (also
[RY20, Ch. 1, §Using Fooling Sets]). Deviation: this is the exponential form of the
fooling-set bound `⌈log₂ |S|⌉ ≤ D(g)`; `clog_ncard_le_communicationComplexity` restates it
with `Nat.clog`. The proof combines the leaf-rectangle partition of a protocol of complexity
at most `n` with the fact that a fooling set meets each monochromatic rectangle in at most
one point. -/
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

/-- Fooling-set lower bound: the deterministic communication complexity of `g` is at least
`⌈log₂ |S|⌉` for every fooling set `S` of `g` [Rou16, Cor 4.7] (also
[RY20, Ch. 1, §Using Fooling Sets]). Deviation: the ceiling logarithm is `Nat.clog 2`, and
the inequality is in `ℕ∞`, so it holds trivially when the complexity is infinite. -/
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
