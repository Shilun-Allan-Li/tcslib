/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSemantics

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Phases for deterministic memory instructions

Each memory schedule is connected to the extended RAM step through the published instruction
and footprint equations. The resulting finite phases have fresh entries and two distinct exits,
with every run taking the next exit and equal transitions under both choices.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_oneMachine`: the constant-one instruction phase.
* `WordRAM.Sim.phase_binaryMachine`: the add, subtract and multiply instruction phases.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The one instruction has a finite fresh-entry phase, with equal choices and a next-exit run
encoding its exact RAM step. -/
theorem phase_oneMachine (a : ℕ) (fn : Bool) (z : ℤ) (hz : InRange a z) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.base (.one z)) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_constantSchedule a fn z 1 hz
  apply phase_memoryMachine a fn (.base (.one z)) 0 (fun _ => z)
    (fun _ i => BitVec.ofInt i.width 1) R
  · intro i
    simp only [XInstr.touches_def, baseTouches_def, Finset.mem_singleton]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z (BitVec.ofInt i.width 1) }, ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf, effect_def]

/-- Each binary arithmetic instruction has a finite fresh-entry phase that loads its two
original operands, computes and stores the result, then exits at next. -/
theorem phase_binaryMachine (a : ℕ) (fn : Bool) (z j k : ℤ)
    (hz : InRange a z) (hj : InRange a j) (hk : InRange a k) (op : PhaseArith) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn
        (.base (match op with | .add => .add z j k | .sub => .sub z j k | .mul => .mul z j k))
        0 false b x i F) (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_binarySchedule a fn z j k hz hj hk op
  apply phase_memoryMachine a fn _ 0 (fun _ => z)
    (fun _ i => op.value (i.cfg.mem j) (i.cfg.mem k)) R
  · intro i
    cases op <;> simp only [XInstr.touches_def, baseTouches_def, Finset.mem_insert_self]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z (op.value (i.cfg.mem j) (i.cfg.mem k)) },
      ?_, rfl, rfl, rfl⟩
    cases op <;> simp only [xstep_def, hf, effect_def, PhaseArith.value_eq]

/-- Indirect load has a fresh-entry phase whose next exit encodes the addressed original-memory
word stored at the immediate destination. -/
theorem phase_loadMachine (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.base (.load z j)) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_loadSchedule a fn z j hz hj
  apply phase_memoryMachine a fn (.base (.load z j)) 0 (fun _ => z)
    (fun _ i => i.cfg.mem (i.cfg.mem j).toInt) R
  · intro i
    simp only [XInstr.touches_def, baseTouches_def, Finset.mem_insert_self]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z (i.cfg.mem (i.cfg.mem j).toInt) }, ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf, effect_def]

/-- Indirect store has a fresh-entry phase whose next exit encodes the original source value
assigned at the signed address in the destination cell. -/
theorem phase_storeMachine (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.base (.store z j)) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_storeSchedule a fn z j hz hj
  apply phase_memoryMachine a fn (.base (.store z j)) 0 (fun i => (i.cfg.mem z).toInt)
    (fun _ i => i.cfg.mem j) R
  · intro i
    have hd : (i.cfg.mem z).toInt ∈ ({z, j, (i.cfg.mem z).toInt} : Finset ℤ) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self (i.cfg.mem z).toInt))
    simpa only [XInstr.touches_def, baseTouches_def] using hd
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem (i.cfg.mem z).toInt (i.cfg.mem j) }, ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf, effect_def]

/-- Signed halving has a fresh-entry phase whose next exit encodes the arithmetic right shift
stored at its immediate destination. -/
theorem phase_halfMachine (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.half z j) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_halfSchedule a fn z j hz hj
  apply phase_memoryMachine a fn (.half z j) 0 (fun _ => z)
    (fun _ i => (i.cfg.mem j).sshiftRight 1) R
  · intro i
    simp only [XInstr.touches_def, Finset.mem_insert_self]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z ((i.cfg.mem j).sshiftRight 1) }, ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf]

/-- Input access has a fresh-entry phase whose next exit encodes the exact extended-RAM input
bit word assigned to the immediate destination. -/
theorem phase_inputMachine (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.rdIn z j) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_inputSchedule a fn z j hz hj
  apply phase_memoryMachine a fn (.rdIn z j) 0 (fun _ => z)
    (fun x i => inBitWord i.width x (i.cfg.mem j).toInt) R
  · intro i
    simp only [XInstr.touches_def, Finset.mem_insert_self]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z (inBitWord i.width x (i.cfg.mem j).toInt) },
      ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf]

end WordRAM.Sim
