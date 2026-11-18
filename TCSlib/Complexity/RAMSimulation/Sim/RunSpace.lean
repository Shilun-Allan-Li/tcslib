/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunSlices

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Visited-cell bounds for the RAM host

The start-up's visited cells are counted once. Subsequent instruction phases use fixed
head origins, so their union is bounded by one interval per tape, independently of the
number of instructions. These lemmas read the deterministic and nondeterministic space
measures through their published equations.

## Main definitions

No new space measure is introduced.

## Main results

* `WordRAM.Sim.runSpace_eq_of_clamped_heads`: a branch with a clamped deterministic head
  trajectory visits exactly the deterministic run's cells.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definition 4.1: visited work-tape cells.)
-/

namespace WordRAM.Sim

open Turing

/-- A branch whose head positions follow a deterministic run through time `t`, then repeat
its last positions, uses exactly that run's space, provided the branch is at least `t` long.

**Proof sketch.** On each tape a visited branch position at time `u` is the source position at
`min u t`. Conversely each source time at most `t` is a valid branch prefix and is fixed by
that minimum. The two visited sets agree; take their cardinalities and sum over tapes. -/
theorem runSpace_eq_of_clamped_heads {K : ℕ} {S H : Type} {x : List Bool}
    (N : NDTM K Bool S) (M : MultiTapeTM K Bool H)
    (w : List Bool) (d : Turing.Cfg K Bool S x) (e : Turing.Cfg K Bool H x) (t : ℕ)
    (ht : t ≤ w.length)
    (hheads : ∀ u ≤ w.length, ∀ j,
      (N.runWith (w.take u) d).workTapePos j = (M.runFrom e (min u t)).workTapePos j) :
    N.spaceUsedWith w d = M.spaceUsed e t := by
  have hvisited : ∀ j, N.visitedWith w d j = M.visitedByTapeHead e t j := by
    intro j
    apply Finset.ext
    intro z
    rw [NDTM.visitedWith_eq, M.mem_visitedByTapeHead_iff]
    constructor
    · intro hz
      obtain ⟨u, hu, hpos⟩ := Finset.mem_image.mp hz
      have hul : u ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
      refine ⟨min u t, min_le_right _ _, ?_⟩
      rw [← hheads u hul j]
      exact hpos
    · rintro ⟨u, hu, hpos⟩
      refine Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hu.trans ht)), ?_⟩
      rw [hheads u (hu.trans ht) j, min_eq_left hu]
      exact hpos
  rw [NDTM.spaceUsedWith_eq, M.spaceUsed_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [M.spaceUsedByTape_eq_card, hvisited j]

/-- The space along a constant choice word is exactly the deterministic slice's space.
No agreement between the machine's two transition functions is required. -/
theorem runSpace_replicate {K : ℕ} {S : Type} {x : List Bool}
    (N : NDTM K Bool S) (b : Bool) (t : ℕ) (d : Turing.Cfg K Bool S x) :
    N.spaceUsedWith (List.replicate t b) d = (N.fixChoice b).spaceUsed d t := by
  apply runSpace_eq_of_clamped_heads
  · rw [List.length_replicate]
  · intro u hu j
    rw [List.take_replicate, runWith_replicate]

/-- Two branch segments with the same head envelope retain that envelope after concatenation
when the first segment restores the starting head vector. Radii therefore do not accumulate
over successive RAM instructions. -/
theorem runEnvelope_append {K : ℕ} {S : Type} {x : List Bool}
    (N : NDTM K Bool S) (w₀ w₁ : List Bool) (d e : Turing.Cfg K Bool S x) (R : ℕ)
    (hr : N.runWith w₀ d = e) (hh : e.workTapePos = d.workTapePos)
    (h₀ : ∀ u ≤ w₀.length, ∀ j,
      |(N.runWith (w₀.take u) d).workTapePos j - d.workTapePos j| ≤ (R : ℤ))
    (h₁ : ∀ u ≤ w₁.length, ∀ j,
      |(N.runWith (w₁.take u) e).workTapePos j - e.workTapePos j| ≤ (R : ℤ)) :
    ∀ u ≤ (w₀ ++ w₁).length, ∀ j,
      |(N.runWith ((w₀ ++ w₁).take u) d).workTapePos j - d.workTapePos j| ≤ (R : ℤ) := by
  intro u hu j
  by_cases hu₀ : u ≤ w₀.length
  · rw [List.take_append_of_le_length hu₀]
    exact h₀ u hu₀ j
  · have hu₁ : u - w₀.length ≤ w₁.length := by rw [List.length_append] at hu; omega
    rw [List.take_append, List.take_of_length_le (by omega), NDTM.runWith_append, hr]
    simpa only [hh] using h₁ (u - w₀.length) hu₁ j

/-- Appending a branch whose heads remain in radius `R` adds at most `K·(2R+1)` visited
cells to the first segment's space. The first segment's space occurs with coefficient one.

**Proof sketch.** Split each visited prefix before or after the first word. Its head belongs
either to the first segment's visited set or to the second segment's interval about its
starting head. Bound the union's cardinality by the sum of cardinalities; `Int.card_Icc`
counts the interval. Sum the resulting inequality over the `K` tapes. -/
theorem runSpace_append_le {K : ℕ} {S : Type} {x : List Bool}
    (N : NDTM K Bool S) (w₀ w₁ : List Bool) (d e : Turing.Cfg K Bool S x) (R : ℕ)
    (hr : N.runWith w₀ d = e)
    (henv : ∀ u ≤ w₁.length, ∀ j,
      |(N.runWith (w₁.take u) e).workTapePos j - e.workTapePos j| ≤ (R : ℤ)) :
    N.spaceUsedWith (w₀ ++ w₁) d ≤ N.spaceUsedWith w₀ d + K * (2 * R + 1) := by
  have hone : ∀ j, (N.visitedWith (w₀ ++ w₁) d j).card ≤
      (N.visitedWith w₀ d j).card + (2 * R + 1) := by
    intro j
    let I := Finset.Icc (e.workTapePos j - (R : ℤ)) (e.workTapePos j + (R : ℤ))
    have hsub : N.visitedWith (w₀ ++ w₁) d j ⊆ N.visitedWith w₀ d j ∪ I := by
      intro z hz
      rw [NDTM.visitedWith_eq] at hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      have hul : u ≤ (w₀ ++ w₁).length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
      by_cases hfirst : u ≤ w₀.length
      · apply Finset.mem_union.mpr; left
        rw [NDTM.visitedWith_eq, List.take_append_of_le_length hfirst]
        exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hfirst), rfl⟩
      · apply Finset.mem_union.mpr; right
        have htail : u - w₀.length ≤ w₁.length := by rw [List.length_append] at hul; omega
        rw [List.take_append, List.take_of_length_le (by omega), NDTM.runWith_append, hr]
        exact Finset.mem_Icc.mpr (by
          obtain ⟨hlo, hhi⟩ := abs_le.mp (henv (u - w₀.length) htail j)
          constructor <;> omega)
    have hcard : I.card = 2 * R + 1 := by
      rw [Int.card_Icc]
      have heq : e.workTapePos j + (R : ℤ) + 1 - (e.workTapePos j - (R : ℤ)) =
          ((2 * R + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [heq, Int.toNat_natCast]
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by rw [hcard]))
  rw [NDTM.spaceUsedWith_eq, NDTM.spaceUsedWith_eq]
  calc
    _ ≤ ∑ j : Fin K, ((N.visitedWith w₀ d j).card + (2 * R + 1)) :=
      Finset.sum_le_sum (fun j _ => hone j)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, Nat.mul_add]

end WordRAM.Sim
