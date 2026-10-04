/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import Mathlib.Probability.UniformOn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hash Function Collision Probability

## Main definitions

- `Functions.Hash.HashSpace`: the space `α → Fin k` of hash functions, carrying the
  uniform product measure

## Main results

- `Functions.Hash.collision_prob_le`: for distinct inputs, a uniformly random hash
  collides with probability at most `1 / k`.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace Functions.Hash

/-- The type of hash functions on `α` with outputs in `Fin k`; as a finite probability
space (instances below) it carries the uniform product measure, so a random element is
a uniformly random function, the shared random `h` of the public-coin equality protocol.
[RY20, Ch. 3, Public-coin protocol (Figure 3.1)] (the shared random function `h`). -/
abbrev HashSpace (α : Type*) (k : ℕ) := α → Fin k

noncomputable instance hashRange.measureSpace (k : ℕ) :
    MeasureSpace (Fin k) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

noncomputable instance hashRange.isProbabilityMeasure (k : ℕ) [NeZero k] :
    IsProbabilityMeasure (volume : Measure (Fin k)) := by
  letI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_neZero k⟩⟩
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  exact ProbabilityTheory.uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty

noncomputable instance hashRange.finiteProbabilitySpace (k : ℕ) [NeZero k] :
    FiniteProbabilitySpace (Fin k) :=
  FiniteProbabilitySpace.of (Fin k)

noncomputable instance hashSpace.finiteProbabilitySpace
    (α : Type*) [Fintype α] (k : ℕ) [NeZero k] :
    FiniteProbabilitySpace (HashSpace α k) := by
  infer_instance

open Classical in
/-- The set of hash functions sending both `x` and `y` to the value `a`, written as a box
(a product of coordinate constraints: `{a}` at `x` and at `y`, everything elsewhere). -/
private def collisionPiece
    {α : Type*} (k : ℕ) (x y : α) (a : Fin k) : Set (HashSpace α k) :=
  Set.pi Set.univ
    (Function.update
      (Function.update (fun _ : α => (Set.univ : Set (Fin k))) x ({a} : Set (Fin k)))
      y
      ({a} : Set (Fin k)))

open Classical in
/-- The collision event `{h | h x = h y}` is the union over the values `a` of the boxes
`collisionPiece k x y a`.

**Proof sketch.** Extensionality in `h`. If `h x = h y`, then `h` lies in the box for the value
`a = h x`: the constraint at `y` is `{h x}`, met because `h y = h x`; the constraint at `x` is
`{h x}`; every other coordinate is unconstrained. Conversely, if `h` lies in the box for some
`a`, reading off the box's constraints at `x` and at `y` gives `h x = a = h y`. -/
private lemma collision_mem_iUnion
    {α : Type*} (k : ℕ) (x y : α) :
    {h : HashSpace α k | h x = h y} = ⋃ a : Fin k, collisionPiece k x y a := by
  ext h
  constructor
  · intro hh
    refine Set.mem_iUnion.2 ?_
    refine ⟨h x, ?_⟩
    intro i
    by_cases hi : i = y
    · subst hi
      simpa [Function.update] using hh.symm
    · by_cases hx : i = x
      · subst hx
        simp [Function.update]
      · simp [Function.update, hi, hx]
  · intro hh
    rcases Set.mem_iUnion.1 hh with ⟨a, ha⟩
    have hx' : h x = a := by
      simpa [Set.mem_pi, Function.update] using ha x
    have hy' : h y = a := by
      simpa [Set.mem_pi, Function.update] using ha y
    exact hx'.trans hy'.symm

open Classical in
/-- The boxes `collisionPiece k x y a` for distinct values `a` are pairwise disjoint
(they prescribe different values at `x`). -/
private lemma collisionPiece_pairwiseDisjoint
    {α : Type*} (k : ℕ) (x y : α) :
    Pairwise fun a b => Disjoint (collisionPiece k x y a) (collisionPiece k x y b) := by
  intro a b hab
  refine Set.disjoint_left.2 ?_
  intro h ha hb
  have hx' : h x = a := by
    simpa [Set.mem_pi, Function.update] using ha x
  have hx'' : h x = b := by
    simpa [Set.mem_pi, Function.update] using hb x
  exact hab (hx'.symm.trans hx'')

/-- Under the uniform measure on `Fin k`, a singleton has measure `1 / k`. -/
private lemma hashRange_singleton_measure
    (k : ℕ) [NeZero k] (a : Fin k) :
    volume ({a} : Set (Fin k)) = (1 : ENNReal) / k := by
  change ProbabilityTheory.uniformOn Set.univ ({a} : Set (Fin k)) = (1 : ENNReal) / k
  rw [ProbabilityTheory.uniformOn_univ]
  simp

/-- Under the uniform measure on `Fin k`, a singleton has real-valued measure `1 / k`. -/
private lemma hashRange_singleton_measureReal
    (k : ℕ) [NeZero k] (a : Fin k) :
    volume.real ({a} : Set (Fin k)) = (1 : ℝ) / k := by
  rw [Measure.real]
  rw [hashRange_singleton_measure]
  rw [ENNReal.toReal_div]
  simp

open Classical in
/-- For `x ≠ y`, the box of hash functions sending both `x` and `y` to `a` has
probability `(1/k)²`.

**Proof sketch.** Step 1: the measure of a box is the product of the coordinate
measures. Step 2: peel off the factors at `x` and at `y` from the product. Step 3: the
remaining coordinates are unconstrained, so their factors are `1`. Step 4: the factors at
`x` and at `y` are the singleton measure `1/k`, giving `(1/k)²`. -/
private lemma collisionPiece_measureReal
    {α : Type*} [Fintype α]
    (k : ℕ) [NeZero k] (x y : α) (hxy : x ≠ y) (a : Fin k) :
    volume.real (collisionPiece k x y a) = ((1 : ℝ) / k) ^ 2 := by
  have hyx : y ≠ x := fun hyx => hxy hyx.symm
  -- the coordinate constraints of the box: `{a}` at `x` and at `y`, `univ` elsewhere
  set S : α → Set (Fin k) :=
    Function.update
      (Function.update (fun _ : α => (Set.univ : Set (Fin k))) x ({a} : Set (Fin k)))
      y ({a} : Set (Fin k)) with hS
  -- Step 1: the measure of a box is the product of the coordinate measures
  have step1 : volume.real (collisionPiece k x y a) = ∏ z, volume.real (S z) :=
    FiniteProbabilitySpace.measureReal_pi_univ S
  -- Step 2: peel off the factors at `x` and at `y`
  have hy_mem : y ∈ (Finset.univ : Finset α).erase x := by
    simp [Finset.mem_erase, hyx]
  have step2 : ∏ z, volume.real (S z) =
      (∏ z ∈ ((Finset.univ : Finset α).erase x).erase y, volume.real (S z))
        * volume.real (S y) * volume.real (S x) := by
    rw [← Finset.prod_erase_mul _ (fun z => volume.real (S z)) (Finset.mem_univ x),
      ← Finset.prod_erase_mul _ (fun z => volume.real (S z)) hy_mem]
  -- Step 3: the remaining coordinates are unconstrained, so their factors are `1`
  have step3 :
      ∏ z ∈ ((Finset.univ : Finset α).erase x).erase y, volume.real (S z) = 1 := by
    refine Finset.prod_eq_one fun z hz => ?_
    have hz_ne_y : z ≠ y := (Finset.mem_erase.1 hz).1
    have hz_ne_x : z ≠ x := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hz)).1
    simp [hS, Function.update, hz_ne_x, hz_ne_y]
  -- Step 4: the factors at `x` and at `y` are the singleton measure `1 / k`
  have hSx : volume.real (S x) = (1 : ℝ) / k := by
    simp [hS, Function.update, hxy, hashRange_singleton_measureReal]
  have hSy : volume.real (S y) = (1 : ℝ) / k := by
    simp [hS, hashRange_singleton_measureReal]
  rw [step1, step2, step3, hSx, hSy]
  ring

/-- For distinct inputs `x ≠ y`, a uniformly random hash function `h : α → Fin k`
collides on them (`h x = h y`) with probability at most `1 / k`; in fact equality holds,
and the proof computes the probability exactly. [RY20, Ch. 3, Public-coin protocol
(Figure 3.1)] (`Pr[h(x) = h(y)] ≤ 2^{-k}` for `x ≠ y`). Deviation: the range is an
arbitrary `Fin k` rather than `{0,1}^k`, so the bound reads `1/k`; equality holds but the
statement is an inequality.

**Proof sketch.** (1) Rewrite the collision event as the union over the values `a` of the
boxes `collisionPiece k x y a` (`collision_mem_iUnion`); the boxes are pairwise disjoint, so
the probability of the union is the sum of their probabilities. (2) Each box has probability
`(1/k)²` (`collisionPiece_measureReal`, which uses `x ≠ y`). (3) The sum of `k` copies of
`(1/k)²` is `1/k`, so the bound holds with equality. -/
theorem collision_prob_le
    (α : Type*) [Fintype α]
    (k : ℕ) [NeZero k] (x y : α) (hxy : x ≠ y) :
    volume.real {h : HashSpace α k | h x = h y} ≤ (1 : ℝ) / k := by
  classical
  let q := Fin k
  -- Step 1: the collision event is a disjoint union of boxes
  rw [collision_mem_iUnion k x y]
  rw [FiniteProbabilitySpace.measureReal_iUnion_fintype _
    (collisionPiece_pairwiseDisjoint k x y)]
  -- Step 2: each box has probability `(1/k)²`
  simp_rw [collisionPiece_measureReal k x y hxy]
  -- Step 3: `k` copies of `(1/k)²` sum to `1/k`
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.univ : Finset q).card : ℕ) : ℝ) = k := by
    simp [q]
  rw [hcard]
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne k)
  have hsum_real : (k : ℝ) * ((1 : ℝ) / k) ^ 2 = (1 : ℝ) / k := by
    field_simp [pow_two, hk_ne]
  exact le_of_eq hsum_real

end Functions.Hash

end CommunicationComplexity
