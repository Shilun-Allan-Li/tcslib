/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseInput

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform allowances for instruction rows

A phase has a common time allowance for memory, multiplication and input access, and a space
allowance for memory and the binary input length. Native rows fit constant multiples of these
allowances, so sequencing adds only constants.

## Main definitions

* `WordRAM.Sim.phaseTime`, `WordRAM.Sim.phaseSpace`: time and radius units for one instruction.

## Main results

* `WordRAM.Sim.phase_memory_charge`: keyed-memory cost fits a constant times the memory unit.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim

/-- The phase time unit: represented memory, word multiplication and read-only input access. -/
def phaseTime (i : PhaseData) (x : List Bool) : ℕ :=
  (i.cells.card + 1) * (i.width + 1) + i.width ^ 2 + x.length + 1

/-- The time unit is the footprint/word product plus the squared word width and input length. -/
theorem phaseTime_eq (i : PhaseData) (x : List Bool) :
    phaseTime i x = (i.cells.card + 1) * (i.width + 1) + i.width ^ 2 + x.length + 1 := rfl

/-- The phase radius unit: represented memory and the binary read-only input length. -/
def phaseSpace (i : PhaseData) (x : List Bool) : ℕ :=
  (i.cells.card + 1) * (i.width + 1) + (Nat.bits x.length).length + 1

/-- The radius unit is the footprint/word product plus the binary input length. -/
theorem phaseSpace_eq (i : PhaseData) (x : List Bool) :
    phaseSpace i x = (i.cells.card + 1) * (i.width + 1) + (Nat.bits x.length).length + 1 := rfl

/-- The memory component of either allowance dominates one word plus one cell. -/
theorem phase_word_memory (i : PhaseData) :
    i.width + 1 ≤ (i.cells.card + 1) * (i.width + 1) := by
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right (i.width + 1)
    (Nat.le_add_left 1 i.cells.card)

/-- Native word, input and memory units fit the common positive time and radius allowances. -/
theorem phase_units (i : PhaseData) (x : List Bool) :
    1 ≤ phaseTime i x ∧ 1 ≤ phaseSpace i x ∧
    i.width + 1 ≤ phaseTime i x ∧ i.width + 1 ≤ phaseSpace i x ∧
    i.width + x.length + 1 ≤ phaseTime i x ∧
    i.width + (Nat.bits x.length).length + 1 ≤ phaseSpace i x ∧
    (i.cells.card + 1) * (i.width + 1) ≤ phaseTime i x ∧
    (i.cells.card + 1) * (i.width + 1) ≤ phaseSpace i x := by
  have hw := phase_word_memory i
  rw [phaseTime_eq, phaseSpace_eq]
  omega

/-- The actual table/key/value charge is at most `a+4` times the footprint/word product. -/
theorem phase_memory_charge (a : ℕ) (i : PhaseData) :
    phaseMemoryCost a i ≤ (a + 4) * ((i.cells.card + 1) * (i.width + 1)) := by
  have h₁ : i.width + a + i.width + 4 ≤ (a + 4) * (i.width + 1) := by nlinarith
  have h₂ : i.width + a + i.width + 2 ≤ (a + 4) * (i.width + 1) := by nlinarith
  calc
    phaseMemoryCost a i =
        i.cells.card * (i.width + a + i.width + 4) + (i.width + a + i.width + 2) := by
      rw [phaseMemoryCost_eq]
      omega
    _ ≤ i.cells.card * ((a + 4) * (i.width + 1)) + (a + 4) * (i.width + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h₁) h₂
    _ = (a + 4) * ((i.cells.card + 1) * (i.width + 1)) := by ring

/-- The native arithmetic time factor is at most three times the common time allowance. -/
theorem phase_arith_charge (op : PhaseArith) (i : PhaseData) (x : List Bool) :
    op.steps i.width ≤ 3 * phaseTime i x := by
  have hw := phase_word_memory i
  cases op <;> rw [PhaseArith.steps_eq, phaseTime_eq] <;> nlinarith

end WordRAM.Sim
