/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseControl
import TCSlib.Complexity.RAMSimulation.Sim.PhaseOperations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Semantic postconditions of instruction phases

The tape schedules describe memory words and register contents. The semantic postcondition
connects their final encoding with the extended RAM step for any program whose current
instruction is the one being simulated and any compatible coin stream.

## Main definitions

* `WordRAM.Sim.PhasePost`: the next RAM step, encoding and selected program counter.

## Main results

* `WordRAM.Sim.phase_post_of_write`: a correct final memory assignment gives the semantic
  next-instruction postcondition.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- The frame encodes the next extended RAM configuration for every matching program and
compatible coin stream, and its program counter agrees with the selected next/jump exit. -/
def PhasePost (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ) (taken b : Bool)
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) : Prop :=
  ∀ (P : XProgram) (ρ : List Bool), P.getD i.cfg.pc (.base .reject) = ins →
    (∀ z : ℤ, ins = .coin z → ρ.getD i.cfg.rd false = b) →
    ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
      Encodes a fn (i.cells ∪ ins.touches i.cfg.mem) c'
        (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
      (if taken then c'.pc = label else c'.pc = i.cfg.pc + 1)

/-- The semantic postcondition quantifies matching fetches and compatible coin streams, then
provides the next configuration, its enlarged encoding and the selected program counter. -/
theorem phasePost_iff (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ) (taken b : Bool)
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) :
    PhasePost a fn ins label taken b x i F ↔
      ∀ (P : XProgram) (ρ : List Bool), P.getD i.cfg.pc (.base .reject) = ins →
        (∀ z : ℤ, ins = .coin z → ρ.getD i.cfg.rd false = b) →
        ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
          Encodes a fn (i.cells ∪ ins.touches i.cfg.mem) c'
            (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
          (if taken then c'.pc = label else c'.pc = i.cfg.pc + 1) := Iff.rfl

/-- A final assignment at a touched address gives the next-instruction postcondition whenever
the RAM step has that memory and output and advances its program counter.

**Proof sketch.** Enlarge the assignment's footprint from `insert z T` to `T ∪ touches` with
`phase_encodes_mono`. The matching RAM step may also update its coin count or control, which
are absent from the tape encoding; `phase_encodes_congr` transfers the encoded memory/output to
that configuration. -/
theorem phase_post_of_write (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ) (b : Bool)
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) (z : ℤ) (v : BitVec i.width)
    (he : Encodes a fn (insert z i.cells) { i.cfg with mem := Function.update i.cfg.mem z v }
      (Function.Embedding.refl _) i.origins (F.cfg ()))
    (hz : z ∈ ins.touches i.cfg.mem)
    (hstep : ∀ (P : XProgram) (ρ : List Bool), P.getD i.cfg.pc (.base .reject) = ins →
      (∀ k : ℤ, ins = .coin k → ρ.getD i.cfg.rd false = b) →
      ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
        c'.mem = Function.update i.cfg.mem z v ∧ c'.out = i.cfg.out ∧ c'.pc = i.cfg.pc + 1) :
    PhasePost a fn ins label false b x i F := by
  apply (phasePost_iff a fn ins label false b x i F).mpr
  intro P ρ hf hc
  obtain ⟨c', hs, hm, ho, hp⟩ := hstep P ρ hf hc
  have hT : insert z i.cells ⊆ i.cells ∪ ins.touches i.cfg.mem := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hq | hq
    · subst q
      exact Finset.mem_union_right _ hz
    · exact Finset.mem_union_left _ hq
  have he' := phase_encodes_mono fn _ _ _ (Function.Embedding.refl _) i.origins (F.cfg ()) he hT
  refine ⟨c', hs, ?_, hp⟩
  exact (phase_encodes_congr fn _ { i.cfg with mem := Function.update i.cfg.mem z v } c'
    (Function.Embedding.refl _) i.origins (F.cfg ()) (F.cfg ()) rfl rfl rfl hm.symm ho.symm).mp he'

/-- A deterministic memory-writing schedule with the specified RAM step semantics gives a
fresh-entry phase with a next exit and an unused jump exit.

**Proof sketch.** `phase_machine_ofBlock` supplies the finite control and two-exit run.
`PhaseMachine.weaken` changes its memory-layout postcondition to `PhasePost` using
`phase_post_of_write`, without changing the machine or its allowance. -/
theorem phase_memoryMachine (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ)
    (z : PhaseData → ℤ) (v : (x : List Bool) → (i : PhaseData) → BitVec i.width)
    (R : PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert (z i) i.cells)
        { i.cfg with mem := Function.update i.cfg.mem (z i) (v x i) }
        (Function.Embedding.refl _) i.origins (F.cfg ())))
    (hz : ∀ i, z i ∈ ins.touches i.cfg.mem)
    (hstep : ∀ (b : Bool) (x : List Bool) (i : PhaseData) (P : XProgram) (ρ : List Bool),
      P.getD i.cfg.pc (.base .reject) = ins →
      (∀ k : ℤ, ins = .coin k → ρ.getD i.cfg.rd false = b) →
      ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
        c'.mem = Function.update i.cfg.mem (z i) (v x i) ∧
        c'.out = i.cfg.out ∧ c'.pc = i.cfg.pc + 1) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn ins label false b x i F) (fun _ _ _ => false)) := by
  obtain ⟨M⟩ := phase_machine_ofBlock R
  apply M.weaken (by intro x i F hp; exact hp)
  intro b x i F he
  exact phase_post_of_write a fn ins label b x i F (z i) (v x i) he (hz i) (hstep b x i)

end WordRAM.Sim
