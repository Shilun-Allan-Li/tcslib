/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Prefixing and wrapping two-exit instruction blocks

Ordinary blocks can precede a word test. A fresh-entry seam wrapper then turns its two native
exits into the phase's next and jump exits, with the same selected branch.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.PhaseBranch.seq`: prefix a branch by an ordinary block.
* `WordRAM.Sim.phase_machine_ofBranch`: add fresh entry and deterministic choice agreement.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The selected yes/no state belongs to the two live exits. -/
theorem phase_branch_mem {S : Type} (yes no : S) (flag : Bool) :
    some (if flag then yes else no) ∈ ({some yes, some no} : Set (Option S)) := by
  cases flag
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  · exact Set.mem_insert_iff.mpr (Or.inl rfl)

/-- An ordinary block followed by a two-exit branch composes through a seam, retaining the
branch flag and adding the constants plus one dispatch.

**Proof sketch.** Run both blocks and apply `phase_reaches_seq` to the second block's two live
exits. Its frame and flag determine the endpoint. Restored intermediate heads give the common
radius center, and the positive phase time unit absorbs the dispatch. -/
theorem PhaseBranch.seq
    {P Q R : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : List Bool → PhaseData → Bool} (A : PhaseBlock P Q) (B : PhaseBranch Q R flag) :
    Nonempty (PhaseBranch P R flag) := by
  classical
  letI := A.finite
  letI := A.decEq
  letI := B.finite
  letI := B.decEq
  refine ⟨⟨A.State ⊕ B.State, inferInstance, inferInstance,
    seamCompTM A.machine A.exit B.machine B.entry, Sum.inl A.entry,
    Sum.inr B.yes, Sum.inr B.no, ?_, A.constant + B.constant + 1, ?_⟩⟩
  · exact fun h => B.distinct (Sum.inr.inj h)
  · intro x i F hp
    obtain ⟨G, hq, hhG, hrA⟩ := A.run x i F hp
    obtain ⟨H, hr, hhH, hrB⟩ := B.run x i G hq
    refine ⟨H, hr, hhH.trans hhG, ?_⟩
    have hs := phase_reaches_seq A.machine B.machine A.entry A.exit B.entry
      (if flag x i then B.yes else B.no) {some B.yes, some B.no} F G H _ _ _ _ hrA hrB
      (phase_branch_mem B.yes B.no (flag x i)) hhG
    have ht : A.constant * phaseTime i x + 1 + B.constant * phaseTime i x ≤
        (A.constant + B.constant + 1) * phaseTime i x := by
      have hu := (phase_units i x).1
      nlinarith
    have he : A.constant * phaseSpace i x + B.constant * phaseSpace i x ≤
        (A.constant + B.constant + 1) * phaseSpace i x := by nlinarith
    simpa only [Set.image_insert_eq, Set.image_singleton, Option.map_some, apply_ite] using
      hs.mono ht he

/-- A two-exit branch gains a never-targeted entry and equal nondeterministic transitions.
The native yes exit is jump and the native no exit is next.

**Proof sketch.** Prefix the branch by the Boolean padding seam, as for a single-exit block.
`phase_seam_fresh` supplies the fresh entry without a second transition analysis. Compose the
zero-time prefix with `phase_reaches_seq`, retain its two-exit cut, and use the deterministic
embedding's fixed-choice equation. -/
theorem phase_machine_ofBranch
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : List Bool → PhaseData → Bool} (R : PhaseBranch P Q flag) :
    Nonempty (PhaseMachine false P (fun _ => Q) (fun _ => flag)) := by
  classical
  letI := R.finite
  letI := R.decEq
  let A : MultiTapeTM 8 Bool Bool :=
    ⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let M := seamCompTM A false R.machine R.entry
  refine ⟨⟨Bool ⊕ R.State, inferInstance, inferInstance, M.toNDTM,
    Sum.inl false, Sum.inr R.no, Sum.inr R.yes, R.constant + 1, ?_, ?_, ?_, ?_⟩⟩
  · exact fun h => R.distinct (Sum.inr.inj h).symm
  · intro b q inp work
    rw [MultiTapeTM.toNDTM_tr]
    exact phase_seam_fresh R.machine R.entry false q inp work
  · intro q hq
    funext inp work
    rw [MultiTapeTM.toNDTM_tr, MultiTapeTM.toNDTM_tr]
  · intro b x i F hp
    obtain ⟨G, hQ, hh, hr⟩ := R.run x i F hp
    have hs := phase_reaches_seq A R.machine false false R.entry
      (if flag x i then R.yes else R.no) {some R.yes, some R.no} F F G 0 0 _ _
      (phase_reaches_zero A (F.cfg false) {some false}) hr
      (phase_branch_mem R.yes R.no (flag x i)) rfl
    have ht : 0 + 1 + R.constant * phaseTime i x ≤ (R.constant + 1) * phaseTime i x := by
      have hu := (phase_units i x).1
      nlinarith
    have he : 0 + R.constant * phaseSpace i x ≤ (R.constant + 1) * phaseSpace i x := by
      nlinarith
    refine ⟨G, hQ, ?_⟩
    rw [phase_toNDTM_fixChoice, Set.pair_comm]
    simpa only [M, Set.image_insert_eq, Set.image_singleton, Option.map_some, apply_ite] using
      hs.mono ht he

end WordRAM.Sim
