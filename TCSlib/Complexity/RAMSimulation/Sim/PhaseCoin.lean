/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseFork

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The single-choice coin instruction phase

One stationary action at the fresh entry remembers the selected bit in finite control. The
registered host then runs the corresponding deterministic constant-word schedule and joins
both returns at next. Subsequent transitions do not inspect the choice.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_choiceMachine`: remember one choice in control while retaining the frame.
* `WordRAM.Sim.phase_encoded_heads`: two encodings with the same origins have the same heads.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- Two frames encoding configurations at the same origins have identical work-head vectors. -/
theorem phase_encoded_heads {a W : ℕ} {x : List Bool} (fn : Bool)
    (T U : Finset ℤ) (c c' : XCfg W) (o : Fin 8 → ℤ) (F G : PhaseFrame x)
    (hF : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ()))
    (hG : Encodes a fn U c' (Function.Embedding.refl _) o (G.cfg ())) :
    G.workTapePos = F.workTapePos := by
  funext j
  have hf := ((encodes_iff a fn T c (Function.Embedding.refl _) o (F.cfg ())).mp hF).1 j
  have hg := ((encodes_iff a fn U c' (Function.Embedding.refl _) o (G.cfg ())).mp hG).1 j
  simpa only [PhaseFrame.cfg_eq] using hg.trans hf.symm

/-- A stationary one-step source remembers the entry choice in one of two live states without
changing its frame. No catalog row supplies this single-choice, live-return control leaf; its
actions use the existing `FinTM.controlAction`.

**Proof sketch.** At the none-valued entry control, transition `b` silently enters `some b`;
every other control halts. Thus no transition targets the entry, and choices agree elsewhere.
The published one-step and control-action equations identify the unchanged frame after one
step. The initial state differs from both exits, and both work-head vectors are fixed. -/
theorem phase_choiceMachine
    (P : (x : List Bool) → PhaseData → PhaseFrame x → Prop) :
    Nonempty (PhaseMachine true P (fun _ => P) (fun b _ _ => b)) := by
  classical
  let N : NDTM 8 Bool (Option Bool) :=
    ⟨none, fun b q _ _ => if q = none then FinTM.controlAction 0 (some (some b))
      else FinTM.controlAction 0 none⟩
  refine ⟨⟨Option Bool, inferInstance, inferInstance, N, none, some false, some true, 1,
    ?_, ?_, ?_, ?_⟩⟩
  · intro h
    have h' := Option.some.inj h
    cases h'
  · intro b q inp work
    by_cases hq : q = none
    · simp only [N, if_pos hq, FinTM.controlAction_def]
      intro h
      exact Option.noConfusion (Option.some.inj h)
    · simp only [N, if_neg hq, FinTM.controlAction_def]
      exact fun h => Option.noConfusion h
  · intro q hq
    have hn : q ≠ none := by
      rcases hq with hq | hq
      · exact hq
      · cases hq
    simp only [N, if_neg hn]
  · intro b x i F hp
    have hstep : (N.fixChoice b).runFrom (F.cfg none) 1 = F.cfg (some b) := by
      rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some (by rw [PhaseFrame.cfg_eq])]
      simp only [NDTM.fixChoice_tr, N, ↓reduceIte]
      simp only [FinTM.controlAction_apply, moveInputPos_zero, PhaseFrame.cfg_eq]
    have hq : (if b then some true else some false) = some b := by cases b <;> rfl
    refine ⟨F, hp, ?_⟩
    rw [hq]
    apply (reachesWithin_iff _ _ _ _ _ _).mpr
    refine ⟨1, by simpa only [one_mul] using (phase_units i x).1, ?_, ?_, hstep⟩
    · intro s hs hm
      have hs' : s = 0 := by omega
      subst s
      rw [MultiTapeTM.runFrom_zero, PhaseFrame.cfg_eq] at hm
      rcases Set.mem_insert_iff.mp hm with h | h
      · exact Option.noConfusion (Option.some.inj h)
      · exact Option.noConfusion (Option.some.inj (Set.mem_singleton_iff.mp h))
    · intro s hs j
      have hs' : s = 0 ∨ s = 1 := by omega
      rcases hs' with rfl | rfl
      · rw [MultiTapeTM.runFrom_zero, sub_self, abs_zero]
        exact Int.natCast_nonneg _
      · rw [hstep, PhaseFrame.cfg_eq, PhaseFrame.cfg_eq, sub_self, abs_zero]
        exact Int.natCast_nonneg _

/-- A coin instruction has exactly one choice-sensitive entry transition, followed by a
deterministic constant-word assignment for that bit and a shared next exit. Its postcondition
also records the extended RAM's consumed coin through the matching step semantics.

**Proof sketch.** `phase_choiceMachine` remembers the fixed choice without changing the frame.
Instantiate `phase_forkMachine` with the two `phase_constantSchedule` branches. The signed
constant words zero and one equal `coinWord`; `xstep_def` and the compatible stream identify
the updated memory and consumed-coin configuration. `phase_post_of_write` transfers the
encoding, which does not store the RAM coin count. -/
theorem phase_coinMachine (a : ℕ) (fn : Bool) (z : ℤ) (hz : InRange a z) :
    Nonempty (PhaseMachine true (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.coin z) 0 false b x i F) (fun _ _ _ => false)) := by
  obtain ⟨A⟩ := phase_choiceMachine (PhaseState a fn (fun _ _ _ => none))
  apply phase_forkMachine A
  · intro value
    let k : ℤ := if value then 1 else 0
    obtain ⟨K⟩ := phase_constantSchedule a fn z k hz
    apply K.weaken
    · intro x i F hp
      obtain ⟨b, hp, hb⟩ := hp
      exact hp
    · intro x i F he b hb
      subst b
      apply phase_post_of_write a fn (.coin z) 0 value x i F z (BitVec.ofInt i.width k) he
      · simp only [XInstr.touches_def, Finset.mem_singleton]
      · intro P ρ hf hc
        have hw : coinWord i.width value = BitVec.ofInt i.width k := by
          rw [coinWord_def]
          dsimp only [k]
          cases value <;> rfl
        refine ⟨{ i.cfg with
          pc := i.cfg.pc + 1
          mem := Function.update i.cfg.mem z (coinWord i.width value)
          rd := i.cfg.rd + 1 }, ?_, ?_, rfl, rfl⟩
        · simp only [xstep_def, hf, hc z rfl]
        · rw [hw]
  · intro b x i F G hp hq
    exact phase_encoded_heads fn i.cells i.cells i.cfg i.cfg i.origins F G
      ((phaseState_iff a fn _ x i F).mp hp).1 ((phaseState_iff a fn _ x i G).mp hq).1

end WordRAM.Sim
