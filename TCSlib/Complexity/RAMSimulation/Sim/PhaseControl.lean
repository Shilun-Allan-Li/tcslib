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

A finite-exit certificate gains a fresh entry and two distinct routed exits. One shared seam
construction handles its one-exit and Boolean specializations; an empty exit slot uses a
never-targeted padding state. The deterministic embedding agrees under both choices.

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
  have hs : Segment M X (fun p => ∀ j, |p j - d.workTapePos j| ≤ (0 : ℤ)) d d 0 :=
    Segment.zero (by intro j; rw [sub_self, abs_zero])
  obtain ⟨hr, hc, he⟩ := (segment_iff _ _ _ _ _ _).mp hs
  exact (reachesWithin_iff _ _ _ _ _ _).mpr ⟨0, le_rfl, hc, he, hr⟩

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

/-- A bounded run avoids any smaller cut formed from its old exits and one never-targeted
state, provided that state is absent initially. -/
theorem phase_reaches_add_unused {S : Type} {x : List Bool} (M : MultiTapeTM 8 Bool S)
    (d : Turing.Cfg 8 Bool S x) (unused : S) (X Y : Set (Option S))
    (B E : ℕ) (post : Turing.Cfg 8 Bool S x) (h : ReachesWithin M d X B E post)
    (ht : ∀ q inp work, (M.tr q inp work).state ≠ some unused)
    (hd : d.state ≠ some unused) (hY : Y ⊆ insert (some unused) X) :
    ReachesWithin M d Y B E post := by
  obtain ⟨t, hb, hc, he, hr⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t, hb, ?_, he, hr⟩
  intro s hs hm
  rcases Set.mem_insert_iff.mp (hY hm) with hu | hx
  · exact phase_run_avoids M unused ht d hd s hu
  · exact hc s hs hx

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
single-exit and branch phase wrappers.

**Proof sketch.** Read the two seam transition equations. Left control either dispatches right
or halts, and right control is renamed by `Sum.inr`; none can target a left Boolean state. -/
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

/-- A finite-exit certificate whose labels route to distinct next/jump slots gains a fresh
entry and equal nondeterministic transitions. A `none` slot is an unused, never-targeted exit.

**Proof sketch.** Place all native exits on the right of one Boolean padding seam; its unused
true state supplies any empty slot. The injective location map preserves distinctness, and
`phase_seam_fresh` supplies entry freshness. Compose the zero-time prefix once, absorb dispatch
into one extra phase unit, and restrict the cut to the two routed slots with
`phase_reaches_add_unused`. Finally `phase_toNDTM_fixChoice` reads each deterministic slice. -/
theorem phase_machine_ofCertificate {E : Type} [Fintype E] [DecidableEq E]
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {selected : List Bool → PhaseData → E} (R : PhaseCertificate E P Q selected)
    (next jump : Option E) (hdistinct : next ≠ jump) (classify : E → Bool)
    (hroute : ∀ e, some e = if classify e then jump else next) :
    Nonempty (PhaseMachine false P (fun _ => Q)
      (fun _ x i => classify (selected x i))) := by
  classical
  letI := R.finite
  letI := R.decEq
  let A : MultiTapeTM 8 Bool Bool :=
    ⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let M := seamCompTM A false R.machine R.entry
  let loc : Option E → Bool ⊕ R.State
    | none => Sum.inl true
    | some e => Sum.inr (R.exit e)
  have hloc : Function.Injective loc := by
    intro u v h
    cases u <;> cases v
    · rfl
    · exact Sum.noConfusion h
    · exact Sum.noConfusion h
    · exact congrArg some (R.exit.injective (Sum.inr.inj h))
  let X : Set (Option (Bool ⊕ R.State)) := Set.range (fun e => some (Sum.inr (R.exit e)))
  have hmem (v : Option E) : some (loc v) ∈ insert (some (Sum.inl true)) X := by
    cases v with
    | none => exact Set.mem_insert _ _
    | some e => exact Set.mem_insert_of_mem _ (Set.mem_range_self e)
  have hcut : ({some (loc next), some (loc jump)} : Set _) ⊆
      insert (some (Sum.inl true)) X := by
    intro q hq
    rcases Set.mem_insert_iff.mp hq with h | h
    · exact h.symm ▸ hmem next
    · exact (Set.mem_singleton_iff.mp h).symm ▸ hmem jump
  refine ⟨⟨Bool ⊕ R.State, inferInstance, inferInstance, M.toNDTM,
    Sum.inl false, loc next, loc jump, R.constant + 1, ?_, ?_, ?_, ?_⟩⟩
  · exact fun h => hdistinct (hloc h)
  · intro b q inp work
    rw [MultiTapeTM.toNDTM_tr]
    exact phase_seam_fresh R.machine R.entry false q inp work
  · intro q hq
    funext inp work
    rw [MultiTapeTM.toNDTM_tr, MultiTapeTM.toNDTM_tr]
  · intro b x i F hp
    obtain ⟨G, hQ, hh, hr⟩ := R.run x i F hp
    have hs := phase_reaches_seq A R.machine false false R.entry (R.exit (selected x i))
      (Set.range (fun e => some (R.exit e))) F F G 0 0 _ _
      (phase_reaches_zero A (F.cfg false) {some false}) hr (Set.mem_range_self _) rfl
    have ht : 0 + 1 + R.constant * phaseTime i x ≤ (R.constant + 1) * phaseTime i x := by
      have hu := (phase_units i x).1
      nlinarith
    have he : 0 + R.constant * phaseSpace i x ≤ (R.constant + 1) * phaseSpace i x := by
      nlinarith
    have hs' : ReachesWithin M (F.cfg (Sum.inl false)) X
        ((R.constant + 1) * phaseTime i x) ((R.constant + 1) * phaseSpace i x)
        (G.cfg (Sum.inr (R.exit (selected x i)))) := by
      simpa only [X, ← Set.range_comp', Option.map_some] using hs.mono ht he
    have hend : Sum.inr (R.exit (selected x i)) =
        if classify (selected x i) then loc jump else loc next := by
      simpa only [apply_ite] using congrArg loc (hroute (selected x i))
    refine ⟨G, hQ, ?_⟩
    rw [phase_toNDTM_fixChoice, ← hend]
    apply phase_reaches_add_unused M _ (Sum.inl true) X _ _ _ _ hs'
      (phase_seam_fresh R.machine R.entry true) _ hcut
    rw [PhaseFrame.cfg_eq]
    exact fun h => Bool.false_ne_true (Sum.inl.inj (Option.some.inj h))

/-- A single-exit block specializes the finite-exit packaging: its unique label is next and
the empty jump slot is never selected. -/
theorem phase_machine_ofBlock
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop} (R : PhaseBlock P Q) :
    Nonempty (PhaseMachine false P (fun _ => Q) (fun _ _ _ => false)) :=
  phase_machine_ofCertificate R (some ()) none (Option.some_ne_none ())
    (fun _ => false) (fun _ => rfl)

end WordRAM.Sim
