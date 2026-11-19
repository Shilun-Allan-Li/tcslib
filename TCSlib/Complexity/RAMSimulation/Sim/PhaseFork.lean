/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseHost
import TCSlib.Complexity.TuringMachine.Build.NDHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Returning from two instruction continuations

The registered nondeterministic phase host runs a source phase, dispatches its selected live
exit to one of two deterministic continuation blocks, and joins their returns at one next exit.
No transition returns to the source entry. This control arrangement is shared by the coin and
output instruction phases.

## Main definitions

* `WordRAM.Sim.PhaseForkNode`: source, Boolean continuation and common return phases.

## Main results

* `WordRAM.Sim.phase_forkMachine`: compose a finite two-exit source with its continuations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- The three kinds of tagged phase in a two-continuation instruction: its source, a selected
Boolean continuation and the shared return phase. -/
inductive PhaseForkNode where
  | source
  | branch (value : Bool)
  | done
  deriving DecidableEq, Fintype

/-- A source phase and two deterministic continuations join at a common next exit. Only the
source entry can have choice-dependent transitions, and only if its own coin flag permits it.

**Proof sketch.** Instantiate `NDTM.phaseHostND` on the source, two continuation blocks and a
halted Boolean return leaf. Redirect the source's next/jump exits to their continuation entries
and both continuation exits to the same return state. The host transition reader transfers
freshness and choice agreement by phase tags. For a fixed slice,
`phase_reaches_inPhase` places the source and selected continuation through `Contract.inPhase`;
`phase_reaches_trans` concatenates their runs. The two dispatches are absorbed into the sum of
the source and both continuation constants plus two. -/
theorem phase_forkMachine {coin : Bool}
    {P : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {Q R : Bool → (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : Bool → List Bool → PhaseData → Bool} (A : PhaseMachine coin P Q flag)
    (banks : ∀ value : Bool, Nonempty (PhaseBlock
      (fun x i F => ∃ b : Bool, Q b x i F ∧ flag b x i = value)
      (fun x i F => ∀ b : Bool, flag b x i = value → R b x i F)))
    (heads : ∀ b x i F G, P x i F → Q b x i G → G.workTapePos = F.workTapePos) :
    Nonempty (PhaseMachine coin P R (fun _ _ _ => false)) := by
  classical
  let B := fun value => Classical.choice (banks value)
  let Ph : PhaseForkNode → Type
    | .source => A.State
    | .branch value => (B value).State
    | .done => Bool
  letI : ∀ p, Fintype (Ph p) := fun p => match p with
    | .source => A.finite
    | .branch value => (B value).finite
    | .done => inferInstance
  letI : ∀ p, DecidableEq (Ph p) := fun p => match p with
    | .source => A.decEq
    | .branch value => (B value).decEq
    | .done => inferInstance
  let Nf : (p : PhaseForkNode) → NDTM 8 Bool (Ph p)
    | .source => A.machine
    | .branch value => (B value).machine.toNDTM
    | .done => ⟨false, fun _ _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let red : (p : PhaseForkNode) → Ph p → Option (Σ p, Ph p)
    | .source, q =>
      if q = A.jump then some ⟨.branch true, (B true).entry⟩
      else if q = A.next then some ⟨.branch false, (B false).entry⟩ else none
    | .branch value, q => if q = ((B value).exit ()) then some ⟨.done, false⟩ else none
    | .done, _ => none
  let q₀ : Σ p, Ph p := ⟨.source, A.entry⟩
  let N := NDTM.phaseHostND Nf q₀ red
  let Mf := fun b p => (Nf p).fixChoice b
  let Y : Set (Option (Σ p, Ph p)) := {some ⟨.done, false⟩, some ⟨.done, true⟩}
  have ynone : none ∉ Y := by
    intro h
    rcases Set.mem_insert_iff.mp h with h | h
    · exact Option.noConfusion h
    · exact Option.noConfusion (Set.mem_singleton_iff.mp h)
  have ytag (p : PhaseForkNode) (hp : p ≠ .done) :
      ∀ r, some r ∈ Y → r.1 ≠ p := by
    intro r hr
    simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq] at hr
    rcases hr with rfl | rfl <;> exact fun h => hp h.symm
  have redtag : ∀ p q target, red p q = some target → target.1 ≠ .source := by
    intro p q target h
    cases p <;> simp only [red] at h <;> (try split_ifs at h) <;>
      cases h <;> intro hf <;> cases hf
  have source_red : ∀ q, some q ∉ ({some A.next, some A.jump} : Set (Option A.State)) →
      red .source q = none := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq, not_or] at hq
    simp only [red, if_neg hq.2, if_neg hq.1]
  have source_some : ∀ q, some q ∈ ({some A.next, some A.jump} : Set (Option A.State)) →
      ∃ target, red .source q = some target ∧ target.1 ≠ .source := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq] at hq
    rcases hq with rfl | rfl
    · refine ⟨⟨.branch false, (B false).entry⟩, ?_, by intro h; cases h⟩
      simp only [red, A.distinct, ↓reduceIte]
    · refine ⟨⟨.branch true, (B true).entry⟩, ?_, by intro h; cases h⟩
      simp only [red, ↓reduceIte]
  have source_target (value : Bool) :
      red .source (if value then A.jump else A.next) = some ⟨.branch value, (B value).entry⟩ := by
    cases value <;> simp only [Bool.false_eq_true, red, A.distinct, ↓reduceIte]
  have source_none : none ∉ ({some A.next, some A.jump} : Set (Option A.State)) := by
    intro h
    rcases Set.mem_insert_iff.mp h with h | h
    · exact Option.noConfusion h
    · exact Option.noConfusion (Set.mem_singleton_iff.mp h)
  refine ⟨⟨(Σ p, Ph p), inferInstance, inferInstance, N, q₀,
    ⟨.done, false⟩, ⟨.done, true⟩,
    A.constant + (B false).constant + (B true).constant + 2, ?_, ?_, ?_, ?_⟩⟩
  · intro h
    have h' := sigma_mk_injective h
    cases h'
  · intro b q inp work
    rcases q with ⟨p, q⟩
    simp only [N, NDTM.phaseHostND_tr]
    cases hred : red p q with
    | some target =>
      intro h
      exact redtag p q target hred (congrArg Sigma.fst (Option.some.inj h))
    | none =>
      simp only [Action.mapState_state]
      cases p with
      | source =>
        intro h
        obtain ⟨s, hs, hq⟩ := Option.map_eq_some_iff.mp h
        have he : s = A.entry := sigma_mk_injective hq
        exact A.fresh b q inp work (hs.trans (congrArg some he))
      | branch value =>
        intro h
        obtain ⟨s, hs, hq⟩ := Option.map_eq_some_iff.mp h
        have bad := congrArg Sigma.fst hq
        cases bad
      | done =>
        intro h
        obtain ⟨s, hs, hq⟩ := Option.map_eq_some_iff.mp h
        have bad := congrArg Sigma.fst hq
        cases bad
  · intro q hq
    rcases q with ⟨p, q⟩
    funext inp work
    simp only [N, NDTM.phaseHostND_tr]
    cases hred : red p q with
    | some target => rfl
    | none =>
      cases p with
      | source =>
        have ha : q ≠ A.entry ∨ coin = false := by
          rcases hq with hq | hc
          · left
            intro h
            apply hq
            subst q
            rfl
          · exact Or.inr hc
        exact congrArg (fun a : Action 8 Bool A.State =>
          a.mapState (fun s => (⟨.source, s⟩ : Σ p, Ph p)))
          (congrFun (congrFun (A.agree q ha) inp) work)
      | branch value => simp only [Nf, MultiTapeTM.toNDTM_tr]
      | done => rfl
  · intro b x i F hp
    obtain ⟨G, hq, hrA⟩ := A.run b x i F hp
    let value := flag b x i
    obtain ⟨H, hr, hh, hrB⟩ := (B value).run x i G ⟨b, hq, rfl⟩
    have hs := phase_reaches_inPhase (Mf b) q₀ red .source A.entry
      (if flag b x i then A.jump else A.next) {some A.next, some A.jump} F G
      (A.constant * phaseTime i x) (A.constant * phaseSpace i x) hrA
      (by simpa only [Set.pair_comm] using phase_branch_mem A.jump A.next (flag b x i))
      source_none source_red source_some ⟨.branch value, (B value).entry⟩
      (source_target value) Y ynone (ytag .source (by decide))
    have hb : ReachesWithin (Mf b (.branch value)) (G.cfg (B value).entry)
        {some ((B value).exit ())} ((B value).constant * phaseTime i x)
        ((B value).constant * phaseSpace i x) (H.cfg ((B value).exit ())) := by
      simpa only [Mf, Nf, phase_toNDTM_fixChoice, Set.range_unique] using hrB
    have ht := phase_reaches_inPhase (Mf b) q₀ red (.branch value) (B value).entry
      ((B value).exit ()) {some ((B value).exit ())} G H ((B value).constant * phaseTime i x)
      ((B value).constant * phaseSpace i x) hb (Set.mem_singleton_iff.mpr rfl)
      (by intro h; exact Option.noConfusion (Set.mem_singleton_iff.mp h))
      (by
        intro q hq
        simp only [Set.mem_singleton_iff, Option.some.injEq] at hq
        simp only [red, if_neg hq])
      (by
        intro q hq
        have he : q = ((B value).exit ()) := Option.some.inj (Set.mem_singleton_iff.mp hq)
        subst q
        exact ⟨⟨.done, false⟩, by simp only [red, ↓reduceIte], by intro h; cases h⟩)
      ⟨.done, false⟩ (by simp only [red, ↓reduceIte]) Y ynone
      (ytag (.branch value) (by intro h; cases h))
    have hrun := phase_reaches_trans (phaseHostTM (Mf b) q₀ red) q₀
      ⟨.branch value, (B value).entry⟩ ⟨.done, false⟩ Y F G H _ _ _ _ hs ht
      (heads b x i F G hp hq)
    have hc : (B value).constant ≤ (B false).constant + (B true).constant := by
      cases value <;> omega
    have htime : (A.constant * phaseTime i x + 1) + ((B value).constant * phaseTime i x + 1) ≤
        (A.constant + (B false).constant + (B true).constant + 2) * phaseTime i x := by
      have hu := (phase_units i x).1
      have hm := Nat.mul_le_mul_right (phaseTime i x) hc
      nlinarith
    have hspace : A.constant * phaseSpace i x + (B value).constant * phaseSpace i x ≤
        (A.constant + (B false).constant + (B true).constant + 2) * phaseSpace i x := by
      have hm := Nat.mul_le_mul_right (phaseSpace i x) hc
      nlinarith
    refine ⟨H, hr b rfl, ?_⟩
    simpa only [N, NDTM.phaseHostND_fixChoice, Mf, Y] using hrun.mono htime hspace

end WordRAM.Sim
