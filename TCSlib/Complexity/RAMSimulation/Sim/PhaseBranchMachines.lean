/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSemantics
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBranching

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The signed branch instruction phase

A branch fetches its operand, tests its signed value and selects the next or jump exit. No
memory or output changes; only the RAM control position changes.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_post_of_read`: connect an unchanged encoded memory/output to its RAM step.
* `WordRAM.Sim.phase_bltzMachine`: the phase for a negative-value branch.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A frame with unchanged encoded memory and output gives the semantic postcondition whenever
the matching RAM step has that memory/output and the selected program counter. -/
theorem phase_post_of_read (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ) (taken b : Bool)
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x)
    (he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()))
    (hstep : ∀ (P : XProgram) (ρ : List Bool), P.getD i.cfg.pc (.base .reject) = ins →
      (∀ k : ℤ, ins = .coin k → ρ.getD i.cfg.rd false = b) →
      ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
        c'.mem = i.cfg.mem ∧ c'.out = i.cfg.out ∧
        (if taken then c'.pc = label else c'.pc = i.cfg.pc + 1)) :
    PhasePost a fn ins label taken b x i F := by
  apply (phasePost_iff a fn ins label taken b x i F).mpr
  intro P ρ hf hc
  obtain ⟨c', hs, hm, ho, hp⟩ := hstep P ρ hf hc
  have he' := phase_encodes_mono fn i.cells (i.cells ∪ ins.touches i.cfg.mem) i.cfg
    (Function.Embedding.refl _) i.origins (F.cfg ()) he Finset.subset_union_left
  exact ⟨c', hs, (phase_encodes_congr fn _ i.cfg c' (Function.Embedding.refl _) i.origins
    (F.cfg ()) (F.cfg ()) rfl rfl rfl hm.symm ho.symm).mp he', hp⟩

/-- Fetching and testing an immediate operand gives a fresh-entry two-exit phase, retaining
the encoded memory and known fetched registers. The sign and output instructions share it. -/
theorem phase_testMachine (a : ℕ) (fn : Bool) (z : ℤ) (hz : InRange a z) (op : PhaseTestKind) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun _ => PhaseState a fn (fun _ i => Function.update
        (Function.update (fun _ => none) 1 (some (keyBits a i.width z))) 2
          (some (bvBits (i.cfg.mem z))))) (fun _ _ i => op.bit (i.cfg.mem z))) := by
  let regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i =>
    Function.update (Function.update (fun _ => none) 1 (some (keyBits a i.width z))) 2
      (some (bvBits (i.cfg.mem z)))
  obtain ⟨F⟩ := phase_fetchBlock a fn (fun _ _ _ => none) z 0 hz
  simp only [phaseMemoryBank_apply] at F
  obtain ⟨T⟩ := phase_testBlock a fn regs (fun i => i.cfg.mem z) op (by intro x i; rfl)
  obtain ⟨FT⟩ := PhaseBranch.seq F T
  exact phase_machine_ofBranch FT

/-- A branch instruction has a finite phase with a fresh entry, equal choices, and the jump
exit exactly when its operand has negative signed value.

**Proof sketch.** Fetch the operand into register two and prefix the native sign test using
`PhaseBranch.seq`. `phase_machine_ofBranch` supplies the fresh entry and maps its yes/no exits
to jump/next. The unchanged encoding transfers through `phase_post_of_read`, while `xstep_def`
and `PhaseTestKind.bit_eq` identify the selected program counter. -/
theorem phase_bltzMachine (a : ℕ) (fn : Bool) (z : ℤ) (label : ℕ) (hz : InRange a z) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.base (.bltz z label)) label
        (PhaseTestKind.sign.bit (i.cfg.mem z)) b x i F)
      (fun _ _ i => PhaseTestKind.sign.bit (i.cfg.mem z))) := by
  let regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i =>
    Function.update (Function.update (fun _ => none) 1 (some (keyBits a i.width z))) 2
      (some (bvBits (i.cfg.mem z)))
  obtain ⟨M⟩ := phase_testMachine a fn z hz .sign
  apply M.weaken (by intro x i F hp; exact hp)
  intro b x i G hp
  apply phase_post_of_read a fn (.base (.bltz z label)) label _ b x i G
    ((phaseState_iff a fn regs x i G).mp hp).1
  intro P ρ hf hc
  refine ⟨{ i.cfg with pc := if (i.cfg.mem z).toInt < 0 then label else i.cfg.pc + 1 },
    ?_, rfl, rfl, ?_⟩
  · simp only [xstep_def, hf]
  · simp only [PhaseTestKind.bit_eq, decide_eq_true_eq]
    split_ifs <;> rfl

end WordRAM.Sim
