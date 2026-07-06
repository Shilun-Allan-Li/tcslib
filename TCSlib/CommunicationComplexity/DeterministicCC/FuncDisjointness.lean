/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.UpperBounds
import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Fintype.Powerset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact Deterministic Communication Complexity of Set Disjointness

## Main results

- `Functions.Disjointness.communicationComplexity_eq`: For `n ≥ 1`, the deterministic
  communication complexity of the set-disjointness function on subsets of `[n]` is exactly `n + 1`.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Functions.Disjointness

open Rectangle
open scoped symmDiff

/-- The set disjointness function on subsets of `[n]`. -/
noncomputable def disjointness (n : ℕ) (X Y : Set (Fin n)) : Bool :=
  by
    classical
    exact decide (Disjoint X Y)

/-- Disjointness is symmetric in Alice's and Bob's inputs. -/
theorem disjointness_comm (n : ℕ) (X Y : Set (Fin n)) :
    disjointness n X Y = disjointness n Y X := by
  simp [disjointness, disjoint_comm]

/-- The candidate fooling set for disjointness: pairs `(X, Xᶜ)`. -/
def foolingSet (n : ℕ) : Set (Set (Fin n) × Set (Fin n)) :=
  {p | p.2 = p.1ᶜ}

/-- The pairs `(X, Xᶜ)` form a fooling set for disjointness. -/
theorem foolingSet_isFoolingSet (n : ℕ) :
    IsFoolingSet (foolingSet n) (disjointness n) := by
  intro R hR hmono p hp q hq
  rcases p with ⟨X, Y⟩
  rcases q with ⟨X', Y'⟩
  simp only [foolingSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq
  rcases hp with ⟨rfl, hpR⟩
  rcases hq with ⟨rfl, hqR⟩
  by_cases hXX' : X = X'
  · subst hXX'
    rfl
  · have hcross := (IsRectangle_iff R).mp hR X X' Xᶜ X'ᶜ hpR hqR
    obtain ⟨i, hi⟩ : (X ∆ X').Nonempty := Set.symmDiff_nonempty.mpr hXX'
    rw [Set.mem_symmDiff] at hi
    rcases hi with hi | hi
    · have hval := hmono X X Xᶜ X'ᶜ hpR hcross.2
      have htrue : disjointness n X Xᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
      have hne : disjointness n X X'ᶜ ≠ true := by
        unfold disjointness
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim
    · have hval := hmono X' X' X'ᶜ Xᶜ hqR hcross.1
      have htrue : disjointness n X' X'ᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X' X'ᶜ)
      have hne : disjointness n X' Xᶜ ≠ true := by
        unfold disjointness
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim

/-- The fooling set for disjointness has size `2^n`. -/
theorem foolingSet_card (n : ℕ) :
    Set.ncard (foolingSet n) = 2 ^ n := by
  let f : Set (Fin n) → Set (Fin n) × Set (Fin n) := fun X => (X, Xᶜ)
  have hf : Function.Injective f := by
    intro X X' h
    exact congrArg Prod.fst h
  calc Set.ncard (foolingSet n)
      = Set.ncard (Set.range f) := by
          congr
          ext p
          rcases p with ⟨X, Y⟩
          simp [f, foolingSet, eq_comm]
    _ = 2 ^ n := by
          simpa [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin] using
            Set.ncard_range_of_injective hf

/-- The deterministic communication complexity of disjointness is at most `n + 1`:
Alice sends her set, and Bob sends one bit for the answer. -/
theorem communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (disjointness n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (disjointness n)
      ≤ Nat.clog 2 (Nat.card (Set (Fin n))) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (disjointness n)
    _ = n + 1 := by
        have hbool : Nat.clog 2 2 = 1 := by native_decide
        simp only [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin,
          Fintype.card_bool, Nat.one_lt_ofNat, Nat.clog_pow]
        rw [hbool]
        norm_num

/-- For `n ≥ 1`, disjointness on subsets of `[n]` has deterministic
communication complexity at least `n + 1`. -/
theorem le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (disjointness n) := by
  apply Deterministic.le_communicationComplexity_of_forall_lt_ncard
  intro Part hPart
  choose rect hrect_mem hrect_in using fun X : Set (Fin n) =>
    monoPartition_point_mem hPart (X, Xᶜ)
  have hrect_inj : Function.Injective rect := by
    intro X X' hXX
    have hsub :=
      foolingSet_isFoolingSet n (rect X) (hPart.1 _ (hrect_mem X)) (hPart.2.1 _ (hrect_mem X))
    have hp : (X, Xᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hrect_in X]
    have hq : (X', X'ᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hXX ▸ hrect_in X']
    exact congrArg Prod.fst (hsub hp hq)
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    simpa [Fintype.card_set, Fintype.card_fin] using
      Set.ncard_range_of_injective hrect_inj
  let i0 : Fin n := ⟨0, hn⟩
  let x0 : Set (Fin n) := {i0}
  let y0 : Set (Fin n) := {i0}
  obtain ⟨R0, hR0_mem, hR0_in⟩ := monoPartition_point_mem hPart (x0, y0)
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨X, rfl⟩
    have hval := monoPartition_values_eq hPart (hrect_mem X) (hrect_in X) hR0_in
    have htrue : disjointness n X Xᶜ = true := by
      simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
    have hne : disjointness n x0 y0 ≠ true := by
      unfold disjointness
      simp only [ne_eq, decide_eq_true_eq]
      intro hdisj
      rw [Set.disjoint_left] at hdisj
      have hnot : i0 ∉ y0 := hdisj (by simp [x0])
      exact hnot (by simp [y0])
    rw [htrue] at hval
    exact (hne hval.symm).elim
  have hinsert : insert R0 (Set.range rect) ⊆ Part :=
    Set.insert_subset hR0_mem (fun R ⟨X, hX⟩ => hX ▸ hrect_mem X)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (insert R0 (Set.range rect)) := by
        rw [Set.ncard_insert_of_notMem hR0_not_diag, himage_card]
        omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)

/-- For `n ≥ 1`, the deterministic communication complexity of
disjointness on subsets of `[n]` is exactly `n + 1`. -/
theorem communicationComplexity_eq (n : ℕ) (hn : 1 ≤ n) :
    Deterministic.communicationComplexity (disjointness n) = n + 1 := by
  apply le_antisymm (communicationComplexity_le n)
  exact le_communicationComplexity n hn

end Functions.Disjointness

end CommunicationComplexity
