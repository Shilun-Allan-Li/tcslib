/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSchedules

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unary and indirect memory instruction schedules

The unary instructions fetch one word, compute into the result register and assign once.
Indirect load uses sign extension and a second lookup; indirect store fetches the value before
constructing its computed destination key.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_unarySchedule`: the shared fetch, compute and store schedule.
* `WordRAM.Sim.phase_halfSchedule`: signed halving and assignment.
* `WordRAM.Sim.phase_inputSchedule`: read-only input access and assignment.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A computation block whose input is the fetched source word and whose result register is
known gives a complete fetch, compute and immediate-store instruction schedule. -/
theorem phase_unarySchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (v : (x : List Bool) → (i : PhaseData) → BitVec i.width)
    (O : PhaseBlock
      (PhaseState a fn (fun _ i => Function.update
        (Function.update (fun _ => none) 1 (some (keyBits a i.width j))) 2
          (some (bvBits (i.cfg.mem j))))) (PhaseState a fn regs))
    (hv : ∀ x i, regs x i 4 = some (bvBits (v x i))) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (v x i) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  obtain ⟨J⟩ := phase_fetchBlock a fn (fun _ _ _ => none) j 0 hj
  simp only [phaseMemoryBank_apply] at J
  obtain ⟨JO⟩ := J.seq O
  obtain ⟨S⟩ := phase_storeImmediateBlock a fn regs z v hz hv
  exact JO.seq S

/-- Signed halving fetches the source word, shifts it right once with sign retention and
assigns the result at its immediate destination. -/
theorem phase_halfSchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z ((i.cfg.mem j).sshiftRight 1) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₁ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i => Function.update
    (Function.update (fun _ => none) 1 (some (keyBits a i.width j))) 2
      (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update (r₁ x i) 4 (some (bvBits ((i.cfg.mem j).sshiftRight 1)))
  obtain ⟨H⟩ := phase_halfBlock a fn r₁ (fun i => i.cfg.mem j) (by intro x i; rfl)
  exact phase_unarySchedule a fn z j hz hj r₂ (fun _ i => (i.cfg.mem j).sshiftRight 1) H
    (by intro x i; rfl)

/-- Input access fetches its signed source position, reads the bit word and assigns it at the
immediate destination, allowing only the read-only input head to finish elsewhere. -/
theorem phase_inputSchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (inBitWord i.width x (i.cfg.mem j).toInt) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₁ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i => Function.update
    (Function.update (fun _ => none) 1 (some (keyBits a i.width j))) 2
      (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update (r₁ x i) 4
    (some (bvBits (inBitWord i.width x (i.cfg.mem j).toInt)))
  obtain ⟨I⟩ := phase_inputBlock a fn r₁ (fun i => i.cfg.mem j) (by intro x i; rfl)
  exact phase_unarySchedule a fn z j hz hj r₂
    (fun x i => inBitWord i.width x (i.cfg.mem j).toInt) I (by intro x i; rfl)

/-- Indirect load fetches a source address word, sign-extends it to a key, looks up the addressed
word and assigns that result at the immediate destination.

**Proof sketch.** The shared unary schedule supplies the first fetch and final store. Its
middle block composes `phase_signExtendBlock` with a lookup into register four, using
`phase_computed_inRange` for the signed indirect address. All reads use the original memory. -/
theorem phase_loadSchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (i.cfg.mem (i.cfg.mem j).toInt) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₁ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i => Function.update
    (Function.update (fun _ => none) 1 (some (keyBits a i.width j))) 2
      (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update (r₁ x i) 1
    (some (keyBits a i.width (i.cfg.mem j).toInt))
  let r₃ := fun x i => Function.update (r₂ x i) 4
    (some (bvBits (i.cfg.mem (i.cfg.mem j).toInt)))
  obtain ⟨E⟩ := phase_signExtendBlock a fn r₁ (fun i => i.cfg.mem j) (by intro x i; rfl)
  obtain ⟨L⟩ := phase_lookupBlock a fn r₂ (fun i => (i.cfg.mem j).toInt) 2
    (by intro x i; rfl) (fun i => phase_computed_inRange a (i.cfg.mem j))
  simp only [phaseMemoryBank_apply] at L
  obtain ⟨EL⟩ := E.seq L
  exact phase_unarySchedule a fn z j hz hj r₃ (fun _ i => i.cfg.mem (i.cfg.mem j).toInt) EL
    (by intro x i; rfl)

/-- Indirect store fetches the value first, then the destination address word, sign-extends that
address to its key and assigns the saved value at that computed destination.

**Proof sketch.** Fetch the value into register four before the destination-address fetch into
two, so key construction cannot overwrite a saved computed key. `phase_signExtendBlock`
constructs the final key; `phase_assignBlock` uses the retained value and the signed-address
range. Sequential block contracts account for all dispatches and preserve the original-memory
meaning of every read. -/
theorem phase_storeSchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert (i.cfg.mem z).toInt i.cells)
        { i.cfg with mem := Function.update i.cfg.mem (i.cfg.mem z).toInt (i.cfg.mem j) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₀ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ _ _ => none
  let r₁ := fun x i => Function.update
    (Function.update (r₀ x i) 1 (some (keyBits a i.width j))) 4 (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update
    (Function.update (r₁ x i) 1 (some (keyBits a i.width z))) 2 (some (bvBits (i.cfg.mem z)))
  let r₃ := fun x i => Function.update (r₂ x i) 1
    (some (keyBits a i.width (i.cfg.mem z).toInt))
  obtain ⟨J⟩ := phase_fetchBlock a fn r₀ j 2 hj
  simp only [phaseMemoryBank_apply] at J
  obtain ⟨Z⟩ := phase_fetchBlock a fn r₁ z 0 hz
  simp only [phaseMemoryBank_apply] at Z
  obtain ⟨E⟩ := phase_signExtendBlock a fn r₂ (fun i => i.cfg.mem z) (by intro x i; rfl)
  obtain ⟨A⟩ := phase_assignBlock a fn r₃ (fun i => (i.cfg.mem z).toInt) (fun _ i => i.cfg.mem j)
    (by intro x i; rfl) (by intro x i; rfl) (fun i => phase_computed_inRange a (i.cfg.mem z))
  obtain ⟨JZ⟩ := J.seq Z
  obtain ⟨JZE⟩ := JZ.seq E
  exact JZE.seq A

end WordRAM.Sim
