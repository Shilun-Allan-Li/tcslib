/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCoin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Optional output in a live instruction phase

The emit instruction tests its operand and, in function mode, appends the selected bit. A
stationary optional-emission leaf keeps all tapes and heads and returns at a live exit.

## Main definitions

* `WordRAM.Sim.PhaseFrame.emit`: append one bit precisely in function mode.

## Main results

* `WordRAM.Sim.phase_emitAction_apply`: the exact frame of a stationary optional emission.
* `WordRAM.Sim.phase_emitBlock`: a live-return optional-emission block.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- Append the selected bit in function mode, leaving all input/work tapes and heads fixed. -/
def PhaseFrame.emit {x : List Bool} (fn bit : Bool) (F : PhaseFrame x) : PhaseFrame x :=
  { F with output := F.output ++ if fn then [bit] else [] }

attribute [simps (config := { isSimp := false }) inputPos workTapes workTapePos output] PhaseFrame.emit

/-- Optional emission changes only the frame's output by the conditional singleton append. -/
theorem PhaseFrame.emit_eq {x : List Bool} (fn bit : Bool) (F : PhaseFrame x) :
    F.emit fn bit = { F with output := F.output ++ if fn then [bit] else [] } := rfl

/-- A stationary, non-writing action with optional emission installs its live or halted control
and appends just that optional output, leaving all other frame fields unchanged. -/
theorem phase_emitAction_apply {S : Type} {x : List Bool} (d : Turing.Cfg 8 Bool S x)
    (q : Option S) (bit : Option Bool) :
    (⟨0, fun _ => (none, 0), bit, q⟩ : Action 8 Bool S).apply d =
      { d with state := q, output := d.output ++ bit.toList } := by
  apply Cfg.ext
  · rw [Action.apply_state]
  · simp only [Action.apply_inputPos, moveInputPos_zero]
  · funext j
    simp only [Action.apply_workTapes, Option.getD_none, Cfg.workTapeSymbols_eq,
      Function.update_eq_self]
  · funext j
    simp only [Action.apply_workTapePos, SignType.coe_zero, add_zero]
  · rw [Action.apply_output]

/-- One stationary optional emission is a live-return block. There is no native catalog row
with this optional-output and live-return frame contract, so its one action is supplied here.

**Proof sketch.** The Boolean entry advances to the Boolean exit in one step.
`phase_emitAction_apply` gives its exact output and unchanged frame; its initial state differs
from the exit and every work head stays fixed. `PhaseBlock.ofRow` absorbs its one step into the
positive phase unit. -/
theorem phase_emitBlock (fn bit : Bool)
    (P : (x : List Bool) → PhaseData → PhaseFrame x → Prop) :
    Nonempty (PhaseBlock P (fun x i G => ∃ F, P x i F ∧ G = F.emit fn bit)) := by
  let M : MultiTapeTM 8 Bool Bool :=
    ⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), if fn then some bit else none, some true⟩⟩
  have hstep {x : List Bool} (F : PhaseFrame x) :
      M.runFrom (F.cfg false) 1 = (F.emit fn bit).cfg true := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some (by rw [PhaseFrame.cfg_eq])]
    change (⟨0, fun _ => (none, 0), if fn then some bit else none, some true⟩ :
      Action 8 Bool Bool).apply (F.cfg false) = _
    rw [phase_emitAction_apply]
    cases fn <;> simp only [PhaseFrame.emit_eq, PhaseFrame.cfg_eq, Bool.false_eq_true,
      ↓reduceIte, Option.toList_none, Option.toList_some]
  let row : PhaseRow (fun _ => PhaseData) (fun {x} i F => P x i F)
      (fun _ F => F.emit fn bit) (fun _ => 1) (fun _ => 0) :=
    ⟨Bool, inferInstance, inferInstance, M, false, true,
      (by intro x i F hp; rw [PhaseFrame.emit_eq]), by
        intro x i F hp
        apply (reachesWithin_iff _ _ _ _ _ _).mpr
        refine ⟨1, le_rfl, ?_, ?_, hstep F⟩
        · intro s hs hm
          have hs' : s = 0 := by omega
          subst s
          rw [MultiTapeTM.runFrom_zero, PhaseFrame.cfg_eq] at hm
          have h : (false : Bool) = true := Option.some.inj (Set.mem_singleton_iff.mp hm)
          cases h
        · intro s hs j
          have hs' : s = 0 ∨ s = 1 := by omega
          rcases hs' with rfl | rfl
          · rw [MultiTapeTM.runFrom_zero, sub_self, abs_zero]
            exact le_rfl
          · rw [hstep, PhaseFrame.cfg_eq, PhaseFrame.cfg_eq, PhaseFrame.emit_eq,
              sub_self, abs_zero]
            exact le_rfl⟩
  apply PhaseBlock.ofRow row 1 (by intro x i F hp; exact hp)
  · intro x i F hp
    exact ⟨F, hp, rfl⟩
  · intro x i
    simpa only [one_mul] using (phase_units i x).1
  · intro x i
    exact Nat.zero_le _

/-- A frame emission preserves the encoding and appends its bit to the RAM output, including
verdict mode where the physical output remains empty.

**Proof sketch.** Read the encoding and its tape-layout predicates through their published
readers. The first six clauses are unchanged because all work tapes and heads are fixed.
The output clause follows from the original output equation by cases on function mode. -/
theorem phase_frame_emit_encodes {a W : ℕ} {x : List Bool} (fn bit : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (F : PhaseFrame x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ())) :
    Encodes a fn T { c with out := c.out ++ [bit] } (Function.Embedding.refl _) o
      ((F.emit fn bit).cfg ()) := by
  simp only [encodes_iff, keyTableAt_iff, tableAt_iff, wordAt_iff,
    PhaseFrame.emit_eq, PhaseFrame.cfg_eq] at he ⊢
  obtain ⟨hpos, htable, hkey, hregs, hlen, hscratch, hout⟩ := he
  refine ⟨hpos, htable, hkey, hregs, hlen, hscratch, ?_⟩
  rw [hout]
  cases fn <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil]

/-- The emit instruction has a finite phase with equal choices and a shared next exit. It
appends its operand's nonzero bit in function mode and retains empty physical output in
verdict mode, while encoding the exact extended RAM step in both modes.

**Proof sketch.** Use the shared `phase_testMachine` with the nonzero test. Each branch of
`phase_forkMachine` runs `phase_emitBlock` for its selected bit; both return to the common next
exit. The branch flag identifies that bit with the RAM's nonzero bit, and
`phase_frame_emit_encodes` maintains the encoding in either output mode. `xstep_def` supplies
the next RAM configuration; enlarge its footprint and ignore its control in the encoding. -/
theorem phase_emitMachine (a : ℕ) (fn : Bool) (z : ℤ) (hz : InRange a z) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.emit z) 0 false b x i F) (fun _ _ _ => false)) := by
  let regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i =>
    Function.update (Function.update (fun _ => none) 1 (some (keyBits a i.width z))) 2
      (some (bvBits (i.cfg.mem z)))
  obtain ⟨A⟩ := phase_testMachine a fn z hz .nonzero
  apply phase_forkMachine A
  · intro value
    obtain ⟨E⟩ := phase_emitBlock fn value (fun x i F => ∃ b : Bool,
      PhaseState a fn regs x i F ∧ PhaseTestKind.nonzero.bit (i.cfg.mem z) = value)
    apply E.weaken (by intro x i F hp; exact hp)
    intro x i G he b hb
    obtain ⟨F, ⟨b₀, hp, hflag⟩, rfl⟩ := he
    have hv : decide (i.cfg.mem z ≠ 0) = value := by
      simpa only [PhaseTestKind.bit_eq] using hflag
    have he' := phase_frame_emit_encodes fn value i.cells i.cfg i.origins F
      ((phaseState_iff a fn regs x i F).mp hp).1
    have he'' := phase_encodes_mono fn i.cells (i.cells ∪ (XInstr.emit z).touches i.cfg.mem)
      { i.cfg with out := i.cfg.out ++ [value] } (Function.Embedding.refl _) i.origins
      ((F.emit fn value).cfg ()) he' Finset.subset_union_left
    apply (phasePost_iff a fn (.emit z) 0 false b x i (F.emit fn value)).mpr
    intro P ρ hf hc
    let c' : XCfg i.width := { i.cfg with
      pc := i.cfg.pc + 1
      out := i.cfg.out ++ [value] }
    refine ⟨c', ?_, ?_, rfl⟩
    · simp only [c', xstep_def, hf, hv]
    · exact (phase_encodes_congr fn _ { i.cfg with out := i.cfg.out ++ [value] } c'
        (Function.Embedding.refl _) i.origins ((F.emit fn value).cfg ())
        ((F.emit fn value).cfg ()) rfl rfl rfl rfl rfl).mp he''
  · intro b x i F G hp hq
    exact phase_encoded_heads fn i.cells i.cells i.cfg i.cfg i.origins F G
      ((phaseState_iff a fn _ x i F).mp hp).1 ((phaseState_iff a fn regs x i G).mp hq).1

end WordRAM.Sim
