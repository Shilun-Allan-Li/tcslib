/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseControl

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Word tests and branching instruction blocks

The sign and nonzero tests inspect a known operand without changing the frame. They have two
live exits, and can be prefixed by an ordinary instruction block through the same seam contract.

## Main definitions

* `WordRAM.Sim.PhaseTestKind`: sign or nonzero testing of a word.
* `WordRAM.Sim.PhaseBranch`: a bounded two-exit deterministic block.

## Main results

* `WordRAM.Sim.phase_embed_state`: installing only a native endpoint state preserves the frame.
* `WordRAM.Sim.PhaseTestKind.native`: the common native word-test interface.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The two native word tests used by branch and output instructions. -/
inductive PhaseTestKind where
  | sign
  | nonzero

/-- The bit returned by the selected sign or nonzero test. -/
def PhaseTestKind.bit {W : ℕ} (op : PhaseTestKind) (u : BitVec W) : Bool :=
  match op with
  | .sign => decide (u.toInt < 0)
  | .nonzero => decide (u ≠ 0)

/-- The sign test reports a negative signed value, and the nonzero test reports a nonzero word. -/
theorem PhaseTestKind.bit_eq {W : ℕ} (op : PhaseTestKind) (u : BitVec W) :
    op.bit u = match op with
      | .sign => decide (u.toInt < 0)
      | .nonzero => decide (u ≠ 0) := rfl

/-- The two native tests share the same untouched-frame, restored-head and linear-bound
interface, with distinct yes and no exits. -/
theorem PhaseTestKind.native (op : PhaseTestKind) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 5 Bool S)
      (entry yes no : S) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (d : Turing.Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → ScratchBlank d →
        ReachesWithin M d {some yes, some no} (C * (W + 1)) (C * (W + 1))
          { d with state := some (if op.bit u then yes else no) } := by
  cases op with
  | sign => simpa only [bit_eq, decide_eq_true_eq] using exists_wordSignTM
  | nonzero => simpa only [bit_eq, decide_eq_true_eq] using exists_wordNonzeroTM

/-- A native endpoint that changes only control embeds to the same host frame with that
control, because selecting and reinstalling a bank leaves its original tape functions intact. -/
theorem phase_embed_state {S : Type} {x : List Bool} (σ : Fin 5 ↪ Fin 8)
    (d : Turing.Cfg 8 Bool S x) (q : Option S) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output { d.select σ with state := q } =
      { d with state := q } := by
  simpa only [Cfg.select_eq, Function.update_eq_self] using
    phase_embed_update σ d q d.inputPos 0 (d.workTapes (σ 0))

/-- A finite deterministic two-exit block returns a frame satisfying its postcondition at the
yes or no exit selected by its indexed Boolean flag, restores heads and obeys phase allowances. -/
structure PhaseBranch
    (P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop)
    (flag : List Bool → PhaseData → Bool) where
  State : Type
  finite : Fintype State
  decEq : DecidableEq State
  machine : MultiTapeTM 8 Bool State
  entry : State
  yes : State
  no : State
  distinct : yes ≠ no
  constant : ℕ
  run : ∀ x i F, P x i F → ∃ G : PhaseFrame x, Q x i G ∧
    G.workTapePos = F.workTapePos ∧
    ReachesWithin machine (F.cfg entry) {some yes, some no}
      (constant * phaseTime i x) (constant * phaseSpace i x)
      (G.cfg (if flag x i then yes else no))

/-- Testing a known operand in register two gives a two-exit block with the selected sign or
nonzero flag, without changing its encoding, known words or frame.

**Proof sketch.** Choose the common native test contract, select the arithmetic tape bank and
supply the known word and encoded blank scratch. `phase_reaches_embed` places its run and
`phase_embed_state` identifies the unchanged frame at its selected exit. The native linear
allowances are bounded by the common phase units. -/
theorem phase_testBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → BitVec i.width) (op : PhaseTestKind)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i))) :
    Nonempty (PhaseBranch (PhaseState a fn regs) (PhaseState a fn regs)
      (fun _ i => op.bit (u i))) := by
  obtain ⟨S, hfin, hdec, M, entry, yes, no, C, hy, hM⟩ := op.native
  letI := hfin
  letI := hdec
  refine ⟨⟨S, inferInstance, inferInstance, embedEmitTM phaseArithBank M,
    entry, yes, no, hy, C, ?_⟩⟩
  intro x i F hp
  obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
  have hw : WordAt ((F.cfg entry).select phaseArithBank) 0 (bvBits (u i)) := by
    apply (phase_wordAt_select phaseArithBank (F.cfg entry) 0 _).mpr
    simpa only [phaseArithBank_apply] using
      (phase_wordAt_frame F entry 2 _).mpr (hregs 2 _ (hu x i))
  have hs := phase_scratch_select phaseArithBank F entry
    (by simp only [phaseArithBank_apply]; decide)
    (phase_frame_scratch fn i.cells i.cfg i.origins F he)
  have hn := hM (u i) ((F.cfg entry).select phaseArithBank)
    (by simp only [Cfg.select_eq, PhaseFrame.cfg_eq]) hw hs
  have hr := phase_reaches_embed phaseArithBank M (F.cfg entry) _ _ _ _ hn
  rw [phase_embed_state] at hr
  refine ⟨F, hp, rfl, ?_⟩
  apply ReachesWithin.mono _ (Nat.mul_le_mul_left C (phase_units i x).2.2.1)
    (Nat.mul_le_mul_left C (phase_units i x).2.2.2.1)
  simpa only [PhaseFrame.cfg_eq] using hr

end WordRAM.Sim
