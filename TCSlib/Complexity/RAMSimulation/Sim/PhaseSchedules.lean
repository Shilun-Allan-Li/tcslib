/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCompute

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Register schedules for memory instructions

An immediate read writes its address key then performs one lookup. Instruction schedules
sequence these reads, compute a result and make one final assignment. The represented memory
is unchanged before the last assignment, so every table scan charges the original footprint.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_fetchBlock`: write an immediate key and load the addressed RAM word.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- Fetching an in-range immediate address writes its key and loads its RAM word into a selected
word register, retaining the encoded memory and other known words. -/
theorem phase_fetchBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : ℤ) (dst : Fin 3) (hz : InRange a z) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i =>
        Function.update (Function.update (regs x i) 1 (some (keyBits a i.width z)))
          (phaseMemoryBank dst 2) (some (bvBits (i.cfg.mem z)))))) := by
  obtain ⟨K⟩ := phase_keyBlock a fn regs z
  obtain ⟨L⟩ := phase_lookupBlock a fn
    (fun x i => Function.update (regs x i) 1 (some (keyBits a i.width z))) (fun _ => z) dst
    (by intro x i; exact Function.update_self ..)
    (fun i => phase_inRange_mono (by omega) hz)
  exact K.seq L

/-- Storing the known result word at an immediate address writes that address key, then performs
one assignment and updates the encoded memory and footprint. -/
theorem phase_storeImmediateBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : ℤ) (v : (x : List Bool) → (i : PhaseData) → BitVec i.width)
    (hz : InRange a z) (hv : ∀ x i, regs x i 4 = some (bvBits (v x i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (v x i) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  obtain ⟨K⟩ := phase_keyBlock a fn regs z
  obtain ⟨A⟩ := phase_assignBlock a fn
    (fun x i => Function.update (regs x i) 1 (some (keyBits a i.width z))) (fun _ => z) v
    (by intro x i; exact Function.update_self ..)
    (by intro x i; simpa only [Function.update_of_ne (by decide : (4 : Fin 8) ≠ 1)] using hv x i)
    (fun i => phase_inRange_mono (by omega) hz)
  exact K.seq A

/-- A constant-word instruction computes its constant on register four, writes its destination
key and assigns that word once. This schedule is shared by `one` and each fixed coin branch. -/
theorem phase_constantSchedule (a : ℕ) (fn : Bool) (z value : ℤ) (hz : InRange a z) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (BitVec.ofInt i.width value) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  obtain ⟨V⟩ := phase_constBlock a fn (fun _ _ _ => none) value
  obtain ⟨S⟩ := phase_storeImmediateBlock a fn
    (fun _ i => Function.update (fun _ => none) 4 (some (bvBits (BitVec.ofInt i.width value))))
    z (fun _ i => BitVec.ofInt i.width value) hz (by intro x i; exact Function.update_self ..)
  exact V.seq S

/-- A binary arithmetic instruction fetches its two original-memory operands, computes the
result and assigns it once at its immediate destination.

**Proof sketch.** Two `phase_fetchBlock` calls load registers two and three. Known-register
updates preserve the first operand during the second fetch. `phase_arithBlock` computes into
register four, and `phase_storeImmediateBlock` makes the sole memory change. `PhaseCertificate.seq`
combines the four blocks and their uniform allowances. -/
theorem phase_binarySchedule (a : ℕ) (fn : Bool) (z j k : ℤ)
    (hz : InRange a z) (hj : InRange a j) (hk : InRange a k) (op : PhaseArith) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (op.value (i.cfg.mem j) (i.cfg.mem k)) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₀ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ _ _ => none
  let r₁ := fun x i => Function.update
    (Function.update (r₀ x i) 1 (some (keyBits a i.width j))) 2 (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update
    (Function.update (r₁ x i) 1 (some (keyBits a i.width k))) 3 (some (bvBits (i.cfg.mem k)))
  let r₃ := fun x i => Function.update (r₂ x i) 4
    (some (bvBits (op.value (i.cfg.mem j) (i.cfg.mem k))))
  obtain ⟨J⟩ := phase_fetchBlock a fn r₀ j 0 hj
  simp only [phaseMemoryBank_apply] at J
  obtain ⟨K⟩ := phase_fetchBlock a fn r₁ k 1 hk
  simp only [phaseMemoryBank_apply] at K
  obtain ⟨O⟩ := phase_arithBlock a fn r₂ (fun i => i.cfg.mem j) (fun i => i.cfg.mem k) op
    (by intro x i; rfl) (by intro x i; rfl)
  obtain ⟨S⟩ := phase_storeImmediateBlock a fn r₃ z
    (fun _ i => op.value (i.cfg.mem j) (i.cfg.mem k)) hz (by intro x i; rfl)
  obtain ⟨JK⟩ := J.seq K
  obtain ⟨JKO⟩ := JK.seq O
  exact JKO.seq S

end WordRAM.Sim
