/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite words cut from a choice schedule

A schedule supplies one Boolean at each absolute time. Finite slices compose by concatenation,
including slices taken beyond a supplied finite word when its defaulted read is the schedule.

## Main definitions

* `WordRAM.Sim.runChoices`: a finite slice of a choice schedule.

## Main results

* `WordRAM.Sim.runChoices_length`: the slice has the specified length.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2: binary choices along a branch.)
-/

namespace WordRAM.Sim

/-- The `n` choices of schedule `χ` beginning at absolute time `s`. -/
def runChoices (χ : ℕ → Bool) (s n : ℕ) : List Bool :=
  (List.range n).map (fun j => χ (s + j))

/-- A choice-schedule slice is the range of offsets mapped to the corresponding choices. -/
theorem runChoices_eq (χ : ℕ → Bool) (s n : ℕ) :
    runChoices χ s n = (List.range n).map (fun j => χ (s + j)) := rfl

/-- The empty slice of a schedule is the empty word. -/
theorem runChoices_zero (χ : ℕ → Bool) (s : ℕ) : runChoices χ s 0 = [] := rfl

/-- A schedule slice contains exactly the specified number of bits. -/
theorem runChoices_length (χ : ℕ → Bool) (s n : ℕ) : (runChoices χ s n).length = n := by
  rw [runChoices_eq, List.length_map, List.length_range]

/-- Splitting a schedule slice after `n` bits gives the initial slice followed by the slice
beginning at time `s + n`. -/
theorem runChoices_append (χ : ℕ → Bool) (s n m : ℕ) :
    runChoices χ s (n + m) = runChoices χ s n ++ runChoices χ (s + n) m := by
  rw [runChoices_eq, List.range_add, List.map_append, List.map_map,
    runChoices_eq, runChoices_eq]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [Nat.add_assoc]
  rfl

/-- A nonempty schedule slice starts with the current choice and continues one time step
later. -/
theorem runChoices_succ (χ : ℕ → Bool) (s n : ℕ) :
    runChoices χ s (n + 1) = χ s :: runChoices χ (s + 1) n := by
  rw [runChoices_eq, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.add_zero, runChoices_eq]
  congr 1
  apply List.map_congr_left
  intro j hj
  change χ (s + (j + 1)) = χ ((s + 1) + j)
  congr 1
  omega

/-- The first bit of a positive-length schedule slice is the choice at its starting time. -/
theorem runChoices_head (χ : ℕ → Bool) (s n : ℕ) (hn : 0 < n) :
    (runChoices χ s n).headD false = χ s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [runChoices_succ]
  rfl

/-- A slice of a constant schedule is the constant choice word of the same length. -/
theorem runChoices_const (b : Bool) (s n : ℕ) :
    runChoices (fun _ => b) s n = List.replicate n b := by
  induction n generalizing s with
  | zero => rw [runChoices_zero, List.replicate_zero]
  | succ n ih => rw [runChoices_succ, List.replicate_succ, ih]

/-- Reading an index inside a schedule slice returns the choice at that absolute time. -/
theorem runChoices_getD (χ : ℕ → Bool) (s n i : ℕ) (hi : i < n) :
    (runChoices χ s n).getD i false = χ (s + i) := by
  rw [runChoices_eq]
  have hi' : i < ((List.range n).map (fun j => χ (s + j))).length := by
    rw [List.length_map, List.length_range]
    exact hi
  rw [List.getD_eq_getElem _ false hi', List.getElem_map, List.getElem_range]

/-- A one-bit schedule slice contains just the current choice. -/
theorem runChoices_one (χ : ℕ → Bool) (s : ℕ) : runChoices χ s 1 = [χ s] := by
  rw [runChoices_succ, runChoices_zero]

/-- The initial slice of the defaulted-read schedule of a finite word is its prefix when
the requested length is within the word. -/
theorem runChoices_take (w : List Bool) (n : ℕ) (hn : n ≤ w.length) :
    runChoices (fun i => w.getD i false) 0 n = w.take n := by
  apply List.ext_getElem (by rw [runChoices_length, List.length_take, min_eq_left hn])
  intro i hi hi'
  have hin : i < n := by rw [runChoices_length] at hi; exact hi
  have h := runChoices_getD (fun j => w.getD j false) 0 n i hin
  rw [Nat.zero_add, List.getD_eq_getElem _ false hi] at h
  change (runChoices (fun j => w.getD j false) 0 n)[i] = w.getD i false at h
  rw [List.getD_eq_getElem _ false (hin.trans_le hn)] at h
  rw [List.getElem_take]
  exact h

end WordRAM.Sim
