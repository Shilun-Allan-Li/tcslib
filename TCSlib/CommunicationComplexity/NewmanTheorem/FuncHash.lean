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

## Main results

- `Functions.Hash.collision_prob_le`: For distinct inputs, a uniformly random hash collides with probability at most `1 / k`.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace Functions.Hash

/-- A hash function on `α` with outputs in `Fin k`. -/
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
private def collisionPiece
    {α : Type*} (k : ℕ) (x y : α) (a : Fin k) : Set (HashSpace α k) :=
  Set.pi Set.univ
    (Function.update
      (Function.update (fun _ : α => (Set.univ : Set (Fin k))) x ({a} : Set (Fin k)))
      y
      ({a} : Set (Fin k)))

open Classical in
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

private lemma hashRange_singleton_measure
    (k : ℕ) [NeZero k] (a : Fin k) :
    volume ({a} : Set (Fin k)) = (1 : ENNReal) / k := by
  change ProbabilityTheory.uniformOn Set.univ ({a} : Set (Fin k)) = (1 : ENNReal) / k
  rw [ProbabilityTheory.uniformOn_univ]
  simp

private lemma hashRange_singleton_measureReal
    (k : ℕ) [NeZero k] (a : Fin k) :
    volume.real ({a} : Set (Fin k)) = (1 : ℝ) / k := by
  rw [Measure.real]
  rw [hashRange_singleton_measure]
  rw [ENNReal.toReal_div]
  simp

open Classical in
private lemma collisionPiece_measureReal
    {α : Type*} [Fintype α]
    (k : ℕ) [NeZero k] (x y : α) (hxy : x ≠ y) (a : Fin k) :
    volume.real (collisionPiece k x y a) = ((1 : ℝ) / k) ^ 2 := by
  have hyx : y ≠ x := fun hyx => hxy hyx.symm
  change volume.real
    (Set.pi Set.univ
      (Function.update
        (Function.update (fun _ : α => (Set.univ : Set (Fin k))) x ({a} : Set (Fin k)))
        y
        ({a} : Set (Fin k)))) = _
  rw [FiniteProbabilitySpace.measureReal_pi_univ]
  rw [← Finset.prod_erase_mul (s := Finset.univ)
    (f := fun z : α =>
      volume.real
        (Function.update
          (Function.update (fun _ : α => (Set.univ : Set (Fin k))) x ({a} : Set (Fin k)))
          y
          ({a} : Set (Fin k)) z))
    (a := x) (by simp)]
  have hy_mem : y ∈ (Finset.univ : Finset α).erase x := by
    simp [Finset.mem_erase, hyx]
  rw [← Finset.prod_erase_mul (s := (Finset.univ : Finset α).erase x)
    (f := fun z : α =>
      volume.real
        (Function.update
          (Function.update (fun _ : α => (Set.univ : Set (Fin k))) x ({a} : Set (Fin k)))
          y
          ({a} : Set (Fin k)) z))
    (a := y) hy_mem]
  have hrest :
      ∏ z ∈ ((Finset.univ : Finset α).erase x).erase y,
        volume.real
          (Function.update
            (Function.update (fun _ : α => (Set.univ : Set (Fin k))) x ({a} : Set (Fin k)))
            y
            ({a} : Set (Fin k)) z) = 1 := by
    refine Finset.prod_eq_one ?_
    intro z hz
    have hz_ne_y : z ≠ y := (Finset.mem_erase.1 hz).1
    have hz_ne_x : z ≠ x := by
      exact (Finset.mem_erase.1 (Finset.mem_of_mem_erase hz)).1
    simp [Function.update, hz_ne_x, hz_ne_y]
  rw [hrest]
  simp [Function.update, hashRange_singleton_measureReal, hxy, pow_two]

/-- For distinct inputs, a uniformly random hash collides with probability `1 / k`. -/
theorem collision_prob_le
    (α : Type*) [Fintype α]
    (k : ℕ) [NeZero k] (x y : α) (hxy : x ≠ y) :
    volume.real {h : HashSpace α k | h x = h y} ≤ (1 : ℝ) / k := by
  classical
  let q := Fin k
  rw [collision_mem_iUnion k x y]
  rw [FiniteProbabilitySpace.measureReal_iUnion_fintype _
    (collisionPiece_pairwiseDisjoint k x y)]
  simp_rw [collisionPiece_measureReal k x y hxy]
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
