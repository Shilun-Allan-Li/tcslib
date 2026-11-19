/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The branch specialization of finite-exit packaging

The common finite-exit packaging turns a word test's false and true labels into the phase's
next and jump exits. No branch-specific seam or bounded-run argument is required.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_branch_mem`: the selected branch belongs to its two live exits.
* `WordRAM.Sim.phase_machine_ofBranch`: add fresh entry and deterministic choice agreement.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The selected yes/no state belongs to the two live exits. -/
theorem phase_branch_mem {S : Type} (yes no : S) (flag : Bool) :
    some (if flag then yes else no) ∈ ({some yes, some no} : Set (Option S)) := by
  cases flag
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  · exact Set.mem_insert_iff.mpr (Or.inl rfl)

/-- A branch specializes finite-exit packaging by routing false to next and true to jump. -/
theorem phase_machine_ofBranch
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : List Bool → PhaseData → Bool} (R : PhaseBranch P Q flag) :
    Nonempty (PhaseMachine false P (fun _ => Q) (fun _ => flag)) :=
  phase_machine_ofCertificate R (some false) (some true)
    (fun h => Bool.false_ne_true (Option.some.inj h)) id (by intro e; cases e <;> rfl)

end WordRAM.Sim
