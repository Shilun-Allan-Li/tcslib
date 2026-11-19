/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBlock

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Atomic blocks for instruction schedules

The native rows become blocks that retain the RAM encoding and track known register words.
Their constants absorb the native allowances into the common instruction units.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_writeBlock`: a register-writing row updates its known-register specification.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A correctly sized register-writing row gives a block that updates the destination's known
word and retains the encoding and all other specified words. -/
theorem phase_writeBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (r : Fin 8) (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4)
    (values : (x : List Bool) → PhaseData → List Bool)
    {pre : ∀ {x : List Bool}, PhaseData → PhaseFrame x → Prop}
    {B E : ∀ {x : List Bool}, PhaseData → ℕ}
    (R : PhaseRow (fun _ => PhaseData) pre (fun {x} i F => F.write r (values x i)) @B @E)
    (C : ℕ) (hP : ∀ x i F, PhaseState a fn regs x i F → pre i F)
    (hw : ∀ x i, (values x i).length = if r = 1 then i.width + a else i.width)
    (hB : ∀ x i, B (x := x) i ≤ C * phaseTime i x)
    (hE : ∀ x i, E (x := x) i ≤ C * phaseSpace i x) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) r (some (values x i))))) := by
  apply PhaseBlock.ofRow R C hP _ hB hE
  intro x i F hp
  simpa only [phaseState_iff] using phase_state_write a fn regs x i F hp r hr₀ hr₁
    (values x i) (hw x i)

/-- Multiplying a native memory charge by its constant fits the common allowance whenever
that allowance dominates the footprint/word product. -/
theorem phase_memory_allowance (a C : ℕ) (i : PhaseData) (U : ℕ)
    (hU : (i.cells.card + 1) * (i.width + 1) ≤ U) :
    C * phaseMemoryCost a i ≤ (C * (a + 4)) * U := by
  calc
    _ ≤ C * ((a + 4) * ((i.cells.card + 1) * (i.width + 1))) :=
      Nat.mul_le_mul_left C (phase_memory_charge a i)
    _ ≤ C * ((a + 4) * U) := Nat.mul_le_mul_left C (Nat.mul_le_mul_left (a + 4) hU)
    _ = (C * (a + 4)) * U := by ring

/-- A fixed integer writer on a compatible selected register gives a block that records the
new exact word and retains all other known register words.

**Proof sketch.** Place `phase_intRow` on the supplied bank. Its readiness and blank scratch
come from the encoding. `phase_writeBlock` retains the invariant, and `phase_units` increases
the native linear allowances. This adapter is shared by key, one and coin word writers. -/
theorem phase_intBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : ℤ) (extra : ℕ) (σ : Fin 5 ↪ Fin 8)
    (hσ : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (σ r).val)
    (hr₀ : 1 ≤ (σ 2).val) (hr₁ : (σ 2).val ≤ 4)
    (hext : ∀ W : ℕ, W + extra = if σ 2 = 1 then W + a else W) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) (σ 2)
        (some (bvBits (BitVec.ofInt (i.width + extra) z)))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_intRow (I := fun _ => PhaseData) (fun i => i.width) z extra σ hσ
  apply phase_writeBlock a fn regs (σ 2) hr₀ hr₁ _ R C
  · intro x i F hp
    have he := ((phaseState_iff a fn regs x i F).mp hp).1
    refine ⟨?_, phase_frame_scratch fn i.cells i.cfg i.origins F he⟩
    rw [hext]
    exact phase_frame_ready fn i.cells i.cfg i.origins F he (σ 2) hr₀ hr₁
  · intro x i
    rw [bvBits_length]
    exact hext i.width
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.1
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.2.1

/-- A fixed integer address is written to the key register, retaining the encoded memory and
all other known registers, with a uniform phase constant. -/
theorem phase_keyBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool)) (z : ℤ) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 1 (some (keyBits a i.width z))))) := by
  simpa only [phaseKeyBank_apply, keyBits_def] using
    phase_intBlock a fn regs z a phaseKeyBank
      (by simp only [phaseKeyBank_apply]; decide)
      (by simp only [phaseKeyBank_apply]; decide)
      (by simp only [phaseKeyBank_apply]; decide)
      (by intro W; rw [phaseKeyBank_apply]; rfl)

/-- A fixed integer is written as a word to result register four, retaining the encoded memory
and all other known registers. -/
theorem phase_constBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool)) (z : ℤ) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 4
        (some (bvBits (BitVec.ofInt i.width z)))))) := by
  simpa only [phaseArithBank_apply, Nat.add_zero] using
    phase_intBlock a fn regs z 0 phaseArithBank
      (by simp only [phaseArithBank_apply]; decide)
      (by simp only [phaseArithBank_apply]; decide)
      (by simp only [phaseArithBank_apply]; decide)
      (by intro W; rw [phaseArithBank_apply]; rfl)

/-- With the addressed key known on tape one, lookup loads its memory word into the chosen
word register and retains the encoding and other known words.

**Proof sketch.** `phase_lookupRow` supplies the placed memory row. `PhaseState` supplies its
key, encoding, readiness and scratch. `phase_writeBlock` updates the known-register map, and
`phase_memory_allowance` absorbs the table charge into the phase units. -/
theorem phase_lookupBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : PhaseData → ℤ) (dst : Fin 3)
    (hk : ∀ x i, regs x i 1 = some (keyBits a i.width (z i)))
    (hz : ∀ i, InRange (i.width + a) (z i)) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) (phaseMemoryBank dst 2)
        (some (bvBits (i.cfg.mem (z i))))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_lookupRow a fn z dst
  have hr : (phaseMemoryBank dst 2).val = dst.val + 2 := by
    rw [phaseMemoryBank_apply]
    rfl
  have hr₀ : 1 ≤ (phaseMemoryBank dst 2).val := by omega
  have hr₁ : (phaseMemoryBank dst 2).val ≤ 4 := by have := dst.isLt; omega
  have hne : phaseMemoryBank dst 2 ≠ 1 := by
    intro h
    have hh := congrArg Fin.val h
    omega
  apply phase_writeBlock a fn regs (phaseMemoryBank dst 2) hr₀ hr₁ _ R (C * (a + 4))
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    refine ⟨he, hregs 1 _ (hk x i), ?_, hz i⟩
    simpa only [if_neg hne] using phase_frame_ready fn i.cells i.cfg i.origins F he
      (phaseMemoryBank dst 2) hr₀ hr₁
  · intro x i
    rw [bvBits_length, if_neg hne]
  · intro x i
    exact phase_memory_allowance a C i _ (phase_units i x).2.2.2.2.2.2.1
  · intro x i
    exact phase_memory_allowance a C i _ (phase_units i x).2.2.2.2.2.2.2

/-- With the address key and value word known in registers one and four, assignment updates
the encoded RAM memory and includes the destination cell in its footprint.

**Proof sketch.** Apply `phase_assignRow` under the known-register preconditions. Its endpoint
satisfies `phase_frame_assign_encodes`; `PhaseBlock.ofRow` retains that postcondition, and
`phase_memory_allowance` bounds the native table charge. -/
theorem phase_assignBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : PhaseData → ℤ) (v : (x : List Bool) → (i : PhaseData) → BitVec i.width)
    (hk : ∀ x i, regs x i 1 = some (keyBits a i.width (z i)))
    (hv : ∀ x i, regs x i 4 = some (bvBits (v x i)))
    (hz : ∀ i, InRange (i.width + a) (z i)) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (fun x i F => Encodes a fn (insert (z i) i.cells)
        { i.cfg with mem := Function.update i.cfg.mem (z i) (v x i) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_assignRow a fn z v
  apply PhaseBlock.ofRow R (C * (a + 4))
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    exact ⟨he, hregs 1 _ (hk x i), hregs 4 _ (hv x i), hz i⟩
  · intro x i F hp
    exact phase_frame_assign_encodes a fn i F ((phaseState_iff a fn regs x i F).mp hp).1
      (z i) (hz i) (v x i)
  · intro x i
    exact phase_memory_allowance a C i _ (phase_units i x).2.2.2.2.2.2.1
  · intro x i
    exact phase_memory_allowance a C i _ (phase_units i x).2.2.2.2.2.2.2

end WordRAM.Sim
