/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSchedules
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Entry and exit control of instruction phases

A deterministic instruction block gains a fresh entry and two distinct exits. The entry is a
one-step seam dispatch that no transition targets; the unused jump exit is also never targeted.
The nondeterministic embedding has equal transitions under both choices.

## Main definitions

* `WordRAM.Sim.PhaseMachine`: a finite phase with fresh entry and two distinguished exits.

## Main results

* `WordRAM.Sim.phase_toNDTM_fixChoice`: fixing a deterministic embedding recovers its machine.
* `WordRAM.Sim.phase_run_avoids`: a state never targeted by a transition is avoided by a run
  that starts elsewhere.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- Fixing either choice of a deterministically embedded machine recovers the original machine,
by its published initial-state and transition equations. -/
theorem phase_toNDTM_fixChoice {S : Type} (M : MultiTapeTM 8 Bool S) (b : Bool) :
    M.toNDTM.fixChoice b = M := by
  have hq : (M.toNDTM.fixChoice b).q₀ = M.q₀ := by
    rw [NDTM.fixChoice_q₀, MultiTapeTM.toNDTM_q₀]
  have ht : (M.toNDTM.fixChoice b).tr = M.tr := by
    funext q inp work
    rw [NDTM.fixChoice_tr, MultiTapeTM.toNDTM_tr]
  calc
    _ = ⟨(M.toNDTM.fixChoice b).q₀, (M.toNDTM.fixChoice b).tr⟩ := rfl
    _ = ⟨M.q₀, M.tr⟩ := by rw [hq, ht]
    _ = M := rfl

/-- Every configuration is reached from itself in zero time and zero radius, with a vacuous
cut for any chosen exit set. -/
theorem phase_reaches_zero {S : Type} {x : List Bool} (M : MultiTapeTM 8 Bool S)
    (d : Turing.Cfg 8 Bool S x) (X : Set (Option S)) : ReachesWithin M d X 0 0 d := by
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨0, le_rfl, ?_, ?_, MultiTapeTM.runFrom_zero⟩
  · intro s hs
    omega
  · intro s hs j
    have hs' : s = 0 := by omega
    subst s
    rw [MultiTapeTM.runFrom_zero, sub_self, abs_zero]
    exact le_rfl

/-- A state that no transition targets is absent from every time of a run launched elsewhere. -/
theorem phase_run_avoids {S : Type} (M : MultiTapeTM 8 Bool S) (q : S)
    (ht : ∀ s inp work, (M.tr s inp work).state ≠ some q) {x : List Bool}
    (d : Turing.Cfg 8 Bool S x) (hd : d.state ≠ some q) (t : ℕ) :
    (M.runFrom d t).state ≠ some q := by
  cases t with
  | zero => simpa only [MultiTapeTM.runFrom_zero] using hd
  | succ t =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (M.runFrom d t).state with
    | none => rw [MultiTapeTM.step_of_halt hs, hs]; exact fun h => Option.noConfusion h
    | some s =>
      rw [MultiTapeTM.step_of_some hs, Action.apply_state]
      exact ht s _ _

/-- Adding a never-targeted exit to a bounded run's cut is valid when the start is elsewhere. -/
theorem phase_reaches_add_unused {S : Type} {x : List Bool} (M : MultiTapeTM 8 Bool S)
    (d : Turing.Cfg 8 Bool S x) (next jump : S) (B E : ℕ) (post : Turing.Cfg 8 Bool S x)
    (h : ReachesWithin M d {some next} B E post)
    (ht : ∀ q inp work, (M.tr q inp work).state ≠ some jump) (hd : d.state ≠ some jump) :
    ReachesWithin M d {some next, some jump} B E post := by
  obtain ⟨t, hb, hc, he, hr⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t, hb, ?_, he, hr⟩
  intro s hs hm
  rcases (Set.mem_insert_iff.mp hm) with hn | hj
  · exact hc s hs (Set.mem_singleton_iff.mpr hn)
  · exact phase_run_avoids M jump ht d hd s (Set.mem_singleton_iff.mp hj)

/-- A finite instruction phase has a never-targeted entry, choice agreement except possibly at
that entry, distinct next/jump exits and bounded fixed-choice runs. Its postcondition and jump
flag may depend on the fixed choice. -/
structure PhaseMachine (coin : Bool)
    (P : (x : List Bool) → PhaseData → PhaseFrame x → Prop)
    (Q : Bool → (x : List Bool) → PhaseData → PhaseFrame x → Prop)
    (takeJump : Bool → List Bool → PhaseData → Bool) where
  State : Type
  finite : Fintype State
  decEq : DecidableEq State
  machine : NDTM 8 Bool State
  entry : State
  next : State
  jump : State
  constant : ℕ
  distinct : next ≠ jump
  fresh : ∀ b q inp work, (machine.tr b q inp work).state ≠ some entry
  agree : ∀ q, q ≠ entry ∨ coin = false → machine.tr false q = machine.tr true q
  run : ∀ b x i F, P x i F → ∃ G : PhaseFrame x, Q b x i G ∧
    ReachesWithin (machine.fixChoice b) (F.cfg entry) {some next, some jump}
      (constant * phaseTime i x) (constant * phaseSpace i x)
      (G.cfg (if takeJump b x i then jump else next))

/-- Strengthening a phase's precondition and weakening its choice-dependent postcondition
retains its finite machine, entry/exit properties and bounds. -/
theorem PhaseMachine.weaken {coin : Bool}
    {P P' : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {Q Q' : Bool → (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : Bool → List Bool → PhaseData → Bool} (M : PhaseMachine coin P Q flag)
    (hP : ∀ x i F, P' x i F → P x i F)
    (hQ : ∀ b x i F, Q b x i F → Q' b x i F) :
    Nonempty (PhaseMachine coin P' Q' flag) := by
  refine ⟨⟨M.State, M.finite, M.decEq, M.machine, M.entry, M.next, M.jump, M.constant,
    M.distinct, M.fresh, M.agree, ?_⟩⟩
  intro b x i F hp
  obtain ⟨G, hq, hr⟩ := M.run b x i F (hP x i F hp)
  exact ⟨G, hQ b x i G hq, hr⟩

/-- The Boolean halted padding leaf of a seam has no transitions back to either of its left
states: the false state dispatches right and the true state halts. This is shared by the
single-exit and branch phase wrappers. -/
theorem phase_seam_fresh {S : Type} (R : MultiTapeTM 8 Bool S) (entry : S) (v : Bool) :
    ∀ q inp work,
      ((seamCompTM (⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ :
        MultiTapeTM 8 Bool Bool) false R entry).tr q inp work).state ≠ some (Sum.inl v) := by
  intro q inp work
  cases q with
  | inl q =>
    rw [seamCompTM_tr_inl]
    by_cases hq : q = false
    · rw [if_pos hq]
      intro h
      exact Sum.noConfusion (Option.some.inj h)
    · rw [if_neg hq]
      simp only [Option.map_none]
      exact fun h => Option.noConfusion h
  | inr q =>
    rw [seamCompTM_tr_inr, Action.mapState_state]
    cases hs : (R.tr q inp work).state with
    | none =>
      simp only [Option.map_none]
      exact fun h => Option.noConfusion h
    | some s =>
      simp only [Option.map_some, ne_eq, Option.some.injEq]
      exact Sum.inr_ne_inl

/-- A deterministic single-exit instruction block gains a fresh entry, an unused jump exit,
and equal nondeterministic transitions under both choices.

**Proof sketch.** Use `seamCompTM` to dispatch immediately from the false state of a halted
Boolean leaf into the block; its true state is the unused jump exit. The leaf needs no
computation, and the seam supplies its dispatch. The seam transition equations prove that no
transition targets either left state. `phase_reaches_seq` composes a zero-time prefix contract
with the block, and `phase_reaches_add_unused` supplies the two-exit cut. Embed deterministically
and use `phase_toNDTM_fixChoice` for each slice. -/
theorem phase_machine_ofBlock
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop} (R : PhaseBlock P Q) :
    Nonempty (PhaseMachine false P (fun _ => Q) (fun _ _ _ => false)) := by
  classical
  letI := R.finite
  letI := R.decEq
  let A : MultiTapeTM 8 Bool Bool :=
    ⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let M := seamCompTM A false R.machine R.entry
  have fresh (v : Bool) : ∀ q inp work, (M.tr q inp work).state ≠ some (Sum.inl v) :=
    phase_seam_fresh R.machine R.entry v
  refine ⟨⟨Bool ⊕ R.State, inferInstance, inferInstance, M.toNDTM,
    Sum.inl false, Sum.inr R.exit, Sum.inl true, R.constant + 1, ?_, ?_, ?_, ?_⟩⟩
  · exact Sum.inr_ne_inl
  · intro b q inp work
    rw [MultiTapeTM.toNDTM_tr]
    exact fresh false q inp work
  · intro q hq
    funext inp work
    rw [MultiTapeTM.toNDTM_tr, MultiTapeTM.toNDTM_tr]
  · intro b x i F hp
    obtain ⟨G, hQ, hh, hr⟩ := R.run x i F hp
    have hzero := phase_reaches_zero A (F.cfg false) {some false}
    have hs := phase_reaches_seq A R.machine false false R.entry R.exit {some R.exit}
      F F G 0 0 _ _ hzero hr (Set.mem_singleton_iff.mpr rfl) rfl
    have ht : 0 + 1 + R.constant * phaseTime i x ≤ (R.constant + 1) * phaseTime i x := by
      have hu := (phase_units i x).1
      nlinarith
    have he : 0 + R.constant * phaseSpace i x ≤ (R.constant + 1) * phaseSpace i x := by
      nlinarith
    have hs' : ReachesWithin M (F.cfg (Sum.inl false)) {some (Sum.inr R.exit)}
        ((R.constant + 1) * phaseTime i x) ((R.constant + 1) * phaseSpace i x)
        (G.cfg (Sum.inr R.exit)) := by
      simpa only [M, Set.image_singleton, Option.map_some] using hs.mono ht he
    refine ⟨G, hQ, ?_⟩
    rw [phase_toNDTM_fixChoice]
    apply phase_reaches_add_unused M _ _ _ _ _ _ hs' (fresh true)
    rw [PhaseFrame.cfg_eq]
    intro h
    have h' := Sum.inl.inj (Option.some.inj h)
    cases h'

end WordRAM.Sim
