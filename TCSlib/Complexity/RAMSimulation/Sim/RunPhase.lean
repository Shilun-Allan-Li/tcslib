/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Phases
import TCSlib.Complexity.RAMSimulation.Sim.RunSlices

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform instruction phases for the simulation host

An ordinary instruction exits to the next position or a jump target. A verdict instruction
halts. This file packages both interfaces into one finite phase family for the host.

## Main definitions

* `WordRAM.Sim.RunPhase`: a finite instruction phase with dispatch and resource clauses.

## Main results

The package keeps the two cases of the RAM step in its endpoint assertion, so the master
induction can use one phase family for deterministic and nondeterministic runs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- A finite phase for `ins`: a live endpoint redirects to the next position (`false`) or the
jump target (`true`), and a verdict endpoint halts with the required output. The heads stay
within a fixed multiple of the table, word and input-length sizes. -/
structure RunPhase (a : ℕ) (fn : Bool) (ins : XInstr) where
  State : Type
  finiteState : Fintype State
  decidableState : DecidableEq State
  machine : NDTM 8 Bool State
  entry : State
  redirect : State → Option Bool
  cost : ℕ
  avoids_entry : isCoin ins = true →
    ∀ (b : Bool) (q : State) inp work, (machine.tr b q inp work).state ≠ some entry
  agrees : ∀ q : State, q ≠ entry ∨ isCoin ins = false →
    machine.tr false q = machine.tr true q
  correct : ∀ (b : Bool) {x : List Bool} {W : ℕ} (P : XProgram) (ρ : List Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool State x),
    P.getD c.pc (.base .reject) = ins → (isCoin ins = true → ρ.getD c.rd false = b) →
    d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
    ∃ (t : ℕ) (d' : Turing.Cfg 8 Bool State x),
      t ≤ cost * ((T.card + 1) * (W + 1) + W ^ 2 + x.length + 1) ∧
      (∀ u < t, ∀ q, ((machine.fixChoice b).runFrom d u).state = some q → redirect q = none) ∧
      (∀ u ≤ t, ∀ j : Fin 8, |((machine.fixChoice b).runFrom d u).workTapePos j - o j| ≤
        (cost * ((T.card + 1) * (W + 1) + (Nat.bits x.length).length + 1) : ℕ)) ∧
      (machine.fixChoice b).runFrom d t = d' ∧
      match xstep P x ρ c with
      | .inl c' => Encodes a fn (T ∪ ins.touches c.mem) c' (Function.Embedding.refl _) o d' ∧
          ∃ (q : State) (jump : Bool), d'.state = some q ∧ redirect q = some jump ∧
            c'.pc = if jump then jumpTarget ins else c.pc + 1
      | .inr v => d'.state = none ∧ d'.output = (if fn then c.out else [v])

attribute [instance] RunPhase.finiteState RunPhase.decidableState

/-- A non-verdict instruction has a uniform phase, obtained from `exists_phase` without
changing its machine or resource bounds.

**Proof sketch.** Redirect the two distinct exits to Boolean next/jump tags. The row's cut
excludes both exits before its endpoint. Its head displacement is measured from the origins
because `Encodes` places every head there. The RAM step and the endpoint encoding are exactly
the clauses of `exists_phase`. -/
theorem runPhase_of_instruction (a : ℕ) (fn : Bool) (ins : XInstr)
    (hins : ImmBound a ins) (hv : isVerdict ins = false) : Nonempty (RunPhase a fn ins) := by
  classical
  obtain ⟨S, hfin, hdec, N, entry, next, jump, C, hne, hentry, hagree, hrow⟩ :=
    exists_phase a fn ins hins hv
  letI := hfin
  letI := hdec
  refine ⟨{
    State := S
    finiteState := hfin
    decidableState := hdec
    machine := N
    entry := entry
    redirect := fun q => if q = next then some false else if q = jump then some true else none
    cost := C
    avoids_entry := fun _ => hentry
    agrees := hagree
    correct := ?_ }⟩
  intro b x W P ρ T c o d hfetch hcoin hd he
  obtain ⟨c', d', hstep, he', hexit, hreach⟩ := hrow b P ρ T c o d hfetch hcoin hd he
  obtain ⟨t, ht, hcut, henv, hrun⟩ := (reachesWithin_iff _ _ _ _ _ _).mp hreach
  have hheads : ∀ j, d.workTapePos j = o j :=
      ((encodes_iff a fn T c (Function.Embedding.refl _) o d).mp he).1
  refine ⟨t, d', ht, ?_, ?_, hrun, ?_⟩
  · intro u hu q hq
    have hqn : q ≠ next := by
      intro h
      apply hcut u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hq, h]
      exact Or.inl True.intro
    have hqj : q ≠ jump := by
      intro h
      apply hcut u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hq, h]
      exact Or.inr True.intro
    simp only [if_neg hqn, if_neg hqj]
  · intro u hu j
    simpa only [hheads j] using henv u hu j
  · rw [hstep]
    refine ⟨he', ?_⟩
    rcases hexit with ⟨hs, hp⟩ | ⟨hs, hp⟩
    · exact ⟨next, false, hs, if_pos rfl, hp⟩
    · refine ⟨jump, true, hs, ?_, hp⟩
      simp only [if_neg hne.symm, if_true]

/-- A verdict instruction has a uniform phase with no redirects. Its deterministic verdict
machine is used under either choice, and its stationary heads satisfy every phase envelope.

**Proof sketch.** Use `exists_verdictPhase` and the deterministic embedding. The verdict row's
constant time is bounded by the phase formula because its size factor is at least one. Its
heads never move, and the encoding supplies their origins. -/
theorem runPhase_of_verdict (a : ℕ) (fn : Bool) (ins : XInstr) (v : Bool)
    (hcoin : isCoin ins = false)
    (hstep : ∀ {x : List Bool} {W : ℕ} (P : XProgram) (ρ : List Bool) (c : XCfg W),
      P.getD c.pc (.base .reject) = ins → xstep P x ρ c = .inr v) :
    Nonempty (RunPhase a fn ins) := by
  obtain ⟨S, hfin, hdec, M, entry, C, hrow⟩ := exists_verdictPhase fn v
  refine ⟨{
    State := S
    finiteState := hfin
    decidableState := hdec
    machine := M.toNDTM
    entry := entry
    redirect := fun _ => none
    cost := C
    avoids_entry := ?_
    agrees := ?_
    correct := ?_ }⟩
  · intro h
    simp only [hcoin, Bool.false_eq_true] at h
  · intro q _
    funext inp work
    rw [MultiTapeTM.toNDTM_tr, MultiTapeTM.toNDTM_tr]
  · intro b x W P ρ T c o d hfetch _ hd he
    obtain ⟨t, ht, hs, ho, hfixed⟩ := hrow a T c o d hd he
    have hheads : ∀ j, d.workTapePos j = o j :=
      ((encodes_iff a fn T c (Function.Embedding.refl _) o d).mp he).1
    refine ⟨t, M.runFrom d t, ?_, ?_, ?_, ?_, ?_⟩
    · apply ht.trans
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.le_add_left _ _
    · intro u hu q hq
      rfl
    · intro u hu j
      rw [runDet_fixChoice, hfixed u hu, hheads j, sub_self, abs_zero]
      exact Nat.cast_nonneg _
    · rw [runDet_fixChoice]
    · rw [hstep P ρ c hfetch]
      exact ⟨hs, ho⟩

/-- The verdict instructions are exactly `accept` and `reject`. -/
theorem runVerdict_cases (ins : XInstr) (h : isVerdict ins = true) :
    ins = .base .accept ∨ ins = .base .reject := by
  rcases ins with i | _ | _ | _ | _
  · cases i <;> simp_all only [isVerdict_def, reduceCtorEq, or_true, true_or]
  all_goals simp only [isVerdict_def, Bool.false_eq_true] at h

/-- Every instruction with bounded immediate addresses has a uniform finite simulation phase.
Ordinary instructions use `exists_phase`; the two verdicts use `exists_verdictPhase`. -/
theorem exists_runPhase (a : ℕ) (fn : Bool) (ins : XInstr) (hins : ImmBound a ins) :
    Nonempty (RunPhase a fn ins) := by
  cases hv : isVerdict ins with
  | false => exact runPhase_of_instruction a fn ins hins hv
  | true =>
    rcases runVerdict_cases ins hv with rfl | rfl
    · apply runPhase_of_verdict a fn (.base .accept) true
      · rw [isCoin_def]
      · intro x W P ρ c hfetch
        rw [xstep_def, hfetch]
    · apply runPhase_of_verdict a fn (.base .reject) false
      · rw [isCoin_def]
      · intro x W P ρ c hfetch
        rw [xstep_def, hfetch]

/-- Every branch of a uniform phase follows the deterministic slice selected by its first
bit. This includes the empty branch and verdict phases, whose choices always agree. -/
theorem RunPhase.branch_slice {a : ℕ} {fn : Bool} {ins : XInstr}
    (R : RunPhase a fn ins) {x : List Bool} (w : List Bool)
    (d : Turing.Cfg 8 Bool R.State x) :
    R.machine.runWith w d = (R.machine.fixChoice (w.headD false)).runFrom d w.length := by
  cases hc : isCoin ins with
  | false =>
    apply NDTM.runWith_eq_fixChoice_runFrom
    intro j hj q hq
    exact R.agrees q (Or.inr hc)
  | true =>
    cases w with
    | nil => rw [List.length_nil, NDTM.runWith_nil, MultiTapeTM.runFrom_zero]
    | cons b w =>
      exact runWith_entry_slice R.machine R.entry (R.avoids_entry hc)
        (fun q hq => R.agrees q (Or.inl hq)) b w d

/-- Every prefix of a phase branch follows the slice selected by the original first bit.
The zero-length prefix is independent of that bit. -/
theorem RunPhase.branch_prefix {a : ℕ} {fn : Bool} {ins : XInstr}
    (R : RunPhase a fn ins) {x : List Bool} (w : List Bool)
    (d : Turing.Cfg 8 Bool R.State x) (u : ℕ) (hu : u ≤ w.length) :
    R.machine.runWith (w.take u) d =
      (R.machine.fixChoice (w.headD false)).runFrom d u := by
  cases u with
  | zero => rw [List.take_zero, NDTM.runWith_nil, MultiTapeTM.runFrom_zero]
  | succ u =>
    cases w with
    | nil => rw [List.length_nil] at hu; omega
    | cons b w =>
      rw [List.take_succ_cons, R.branch_slice, List.length_cons,
        List.length_take_of_le (Nat.le_of_succ_le_succ hu)]

/-- A phase prefix follows any fixed choice agreeing with its first actual coin-entry bit.
No first-bit condition is needed for an empty branch or a non-coin instruction. -/
theorem RunPhase.branch_prefix_choice {a : ℕ} {fn : Bool} {ins : XInstr}
    (R : RunPhase a fn ins) {x : List Bool} (b : Bool) (w : List Bool)
    (d : Turing.Cfg 8 Bool R.State x)
    (hb : isCoin ins = true → w ≠ [] → w.headD false = b) (u : ℕ) (hu : u ≤ w.length) :
    R.machine.runWith (w.take u) d = (R.machine.fixChoice b).runFrom d u := by
  cases hc : isCoin ins with
  | false =>
    have h := NDTM.runWith_eq_fixChoice_runFrom R.machine b (w.take u) d
      (fun _ _ q _ => R.agrees q (Or.inr hc))
    simpa only [List.length_take_of_le hu] using h
  | true =>
    cases w with
    | nil =>
      rw [List.length_nil] at hu
      have hz : u = 0 := by omega
      subst u
      rw [List.take_zero, NDTM.runWith_nil, MultiTapeTM.runFrom_zero]
    | cons c w =>
      rw [R.branch_prefix _ d u hu, hb hc (fun h => List.noConfusion h)]

end WordRAM.Sim
