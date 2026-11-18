/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseAtoms

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Arithmetic and input blocks

The computation blocks read the known operand words and record their result while retaining
the represented RAM memory. Arithmetic and input costs fit the common phase allowances.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_arithBlock`: addition, subtraction or multiplication into register four.
* `WordRAM.Sim.phase_sourceBlock`: a shared adapter for one-source linear word rows.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- Binary arithmetic on two known operand words records its result on register four, retaining
the RAM encoding and other known words.

**Proof sketch.** Apply `phase_arithRow` using the two known operands, encoded destination
readiness and blank scratch. `phase_writeBlock` maintains the register invariant.
`phase_arith_charge` absorbs multiplication's quadratic time; radius remains linear. -/
theorem phase_arithBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u v : (i : PhaseData) → BitVec i.width) (op : PhaseArith)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i)))
    (hv : ∀ x i, regs x i 3 = some (bvBits (v i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 4
        (some (bvBits (op.value (u i) (v i))))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_arithRow (I := fun _ => PhaseData) (fun i => i.width) u v op
  apply phase_writeBlock a fn regs 4 (by decide) (by decide) _ R (C * 3)
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    exact ⟨hregs 2 _ (hu x i), hregs 3 _ (hv x i),
      phase_frame_ready fn i.cells i.cfg i.origins F he 4 (by decide) (by decide),
      phase_frame_scratch fn i.cells i.cfg i.origins F he⟩
  · intro x i
    rw [bvBits_length, if_neg (by decide)]
  · intro x i
    calc
      _ ≤ C * (3 * phaseTime i x) := Nat.mul_le_mul_left C (phase_arith_charge op i x)
      _ = (C * 3) * phaseTime i x := by ring
  · intro x i
    exact (Nat.mul_le_mul_left C (phase_units i x).2.2.2.1).trans
      (Nat.mul_le_mul_right _ (by omega : C ≤ C * 3))

/-- A linear row reading register two and writing one compatible register gives a block that
retains the encoding and records its result. The adapter is shared by half and sign extension. -/
theorem phase_sourceBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → List Bool) (r : Fin 8) (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4)
    (values : (i : PhaseData) → List Bool) (C : ℕ)
    (R : PhaseRow (fun _ => PhaseData)
      (fun i F => WordAt (F.cfg ()) 2 (u i) ∧
        PhaseReady (if r = 1 then i.width + a else i.width) r F ∧ PhaseScratch F)
      (fun i F => F.write r (values i))
      (fun i => C * (i.width + 1)) (fun i => C * (i.width + 1)))
    (hu : ∀ x i, regs x i 2 = some (u i))
    (hw : ∀ i, (values i).length = if r = 1 then i.width + a else i.width) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) r (some (values i))))) := by
  apply phase_writeBlock a fn regs r hr₀ hr₁ _ R C
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    exact ⟨hregs 2 _ (hu x i),
      phase_frame_ready fn i.cells i.cfg i.origins F he r hr₀ hr₁,
      phase_frame_scratch fn i.cells i.cfg i.origins F he⟩
  · intro x i
    exact hw i
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.1
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.2.1

/-- Arithmetic halving of a known operand records its signed right shift on register four. -/
theorem phase_halfBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → BitVec i.width)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 4
        (some (bvBits ((u i).sshiftRight 1)))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_halfRow (I := fun _ => PhaseData) (fun i => i.width) u
  exact phase_sourceBlock a fn regs (fun i => bvBits (u i)) 4 (by decide) (by decide)
    (fun i => bvBits ((u i).sshiftRight 1)) C R hu
    (by intro i; rw [bvBits_length, if_neg (by decide)])

/-- Sign-extending a known word writes the key of its signed address on register one. -/
theorem phase_signExtendBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → BitVec i.width)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 1
        (some (keyBits a i.width (u i).toInt))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_signExtendRow (I := fun _ => PhaseData) (fun i => i.width) u a
  simpa only [phase_keyBits_signExtend] using
    phase_sourceBlock a fn regs (fun i => bvBits (u i)) 1 (by decide) (by decide)
      (fun i => bvBits ((u i).signExtend (i.width + a))) C R hu
      (by intro i; rw [bvBits_length, if_pos rfl])

/-- Reading the input at a known signed position writes its bit word on register four, retaining
the RAM encoding and the other known registers while allowing the input head to move.

**Proof sketch.** Supply `phase_inputRow` with the known position, encoded input-length word,
ready result register and blank scratch. `phase_state_write` establishes the resulting known
word; `phase_state_inputPos` permits the native input-head endpoint. The native input time and
radius units are dominated by `phase_units`. -/
theorem phase_inputBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → BitVec i.width)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 4
        (some (bvBits (inBitWord i.width x (u i).toInt)))))) := by
  obtain ⟨C, ip, ⟨R⟩⟩ := phase_inputRow (I := fun _ => PhaseData) (fun i => i.width) u
  apply PhaseBlock.ofRow R C
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    have hh := (encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
      i.origins (F.cfg ())).mp he
    exact ⟨hregs 2 _ (hu x i), hh.2.2.2.2.1,
      phase_frame_ready fn i.cells i.cfg i.origins F he 4 (by decide) (by decide),
      phase_frame_scratch fn i.cells i.cfg i.origins F he⟩
  · intro x i F hp
    have hw : PhaseState a fn
        (fun y j => Function.update (regs y j) 4
          (some (bvBits (inBitWord j.width y (u j).toInt)))) x i
        (F.write 4 (bvBits (inBitWord i.width x (u i).toInt))) := by
      simpa only [phaseState_iff] using phase_state_write a fn regs x i F hp 4
        (by decide) (by decide) (bvBits (inBitWord i.width x (u i).toInt))
        (by rw [bvBits_length, if_neg (by decide)])
    exact phase_state_inputPos a fn _ x i _ hw (ip i F)
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.2.2.1
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.2.2.2.1

end WordRAM.Sim
