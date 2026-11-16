/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.CfgFacts
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Clean modules: subroutine calls that first halt cleanly

A *clean module* computes on a canonical state word: started from the word `arg` on tape zero
(every other tape blank, every head at the origin), it first halts at a positive time within a
budget, leaving the canonical state word of `result arg` and having emitted `emit arg`. Clean
modules are what a finite host can call one after another on one shared bank of tapes.

The clean-call bridges of `TCSlib.Complexity.TuringMachine.Build.Loop`
(`Turing.FinTM.exists_installCallTM`, `Turing.FinTM.exists_emitCallTM`) return to an exit state
instead of halting. The *release-flag stop adapter* `Turing.FinTM.stopTM` turns such a positive
first return into a first halt, so every polynomial-time function has a clean install module and
a clean emit module with polynomial budgets. This is construction glue for the machine model of
[AB09, §1.2], not itself a result of the book.

## Main definitions

* `Turing.FinTM.CleanModule` — a clean module for a result, an emission and a budget.
* `Turing.FinTM.stopTM` — the release-flag stop adapter.

## Main results

* `Turing.MultiTapeTM.exists_first_halt_pos` — a run that starts live and has halted first
  halts at a positive time.
* `Turing.MultiTapeTM.avoid_add` — avoiding a state across a seam.
* `Turing.FinTM.stopTM_runFrom_clean`, `Turing.FinTM.CleanModule.of_stop` — a guarded positive
  return becomes a clean first halt one step later.
* `Complexity.exists_cleanInstall`, `Complexity.exists_cleanEmit` — clean install and emit
  modules for every polynomial-time function.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2.)
-/

namespace Turing

namespace MultiTapeTM

/-- **A positive first halt**: if a run starts live and has halted by time `t`, it first halts
at some time `u` with `0 < u ≤ t`; it is live before `u`, and its configuration at `u` is its
configuration at `t`.

**Proof sketch.** `Turing.MultiTapeTM.exists_first_halt` gives the first halt `u ≤ t`; `u = 0`
would make the live start halted. -/
theorem exists_first_halt_pos {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  obtain ⟨u, hu, hg, he⟩ := MultiTapeTM.exists_first_halt tm cfg hhalt
  have hp : 0 < u := by
    by_contra hn
    have hz : u = 0 := by omega
    have hs := congrArg Cfg.state he
    rw [hz, MultiTapeTM.runFrom_zero, hhalt] at hs
    exact hstart hs
  exact ⟨u, hp, hu, hg, he⟩

/-- **Avoiding a state across a seam**: if a run avoids `anchor` during its first `a` steps and
reaches `d`, and the run from `d` avoids `anchor` during its first `b` steps, then the whole run
avoids `anchor` during its first `a + b` steps.

**Proof sketch.** Both pieces are segments avoiding `{some anchor}` (`Turing.segment_iff`);
concatenate them with `Turing.Segment.trans`. -/
theorem avoid_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  have h₁ : Turing.Segment tm {some anchor} (fun _ => True) c d a :=
    (Turing.segment_iff tm {some anchor} (fun _ => True) c d a).mpr
      ⟨he, fun v hv hm => ha v hv (Set.mem_singleton_iff.mp hm), fun _ _ => True.intro⟩
  have h₂ : Turing.Segment tm {some anchor} (fun _ => True) d (tm.runFrom d b) b :=
    (Turing.segment_iff tm {some anchor} (fun _ => True) d (tm.runFrom d b) b).mpr
      ⟨rfl, fun v hv hm => hb v hv (Set.mem_singleton_iff.mp hm), fun _ _ => True.intro⟩
  have h := (Turing.segment_iff tm {some anchor} (fun _ => True) c (tm.runFrom d b)
    (a + b)).mp (Turing.Segment.trans h₁ h₂)
  intro v hv hm
  exact h.2.1 v hv (Set.mem_singleton_iff.mpr hm)

end MultiTapeTM

namespace FinTM

/-- **A clean module** for `result`, `emit` and budget `B`: `M` has a work tape, and from every
input `x` and every argument `arg` stored as the canonical state word in its start state, it first
halts at a positive time `t ≤ B |arg|`, leaving the canonical state word of `result arg` (every
head at the origin) and having emitted exactly `emit arg`. -/
structure CleanModule (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) :
    Prop where
  /-- The module has a work tape, which holds the state word. -/
  pos : 0 < M.k
  /-- Every call first halts cleanly within the budget. -/
  run : ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- **The release-flag stop adapter** of `C` from `entry` to `exit`: it runs `C` from `entry`
with a release flag that the first step raises, and halts silently on the first visit to `exit`
made after at least one step (so `entry = exit` is allowed). -/
def stopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-! The adapter's tape count as an equation: `(stopTM C entry exit).k = C.k`. -/
attribute [simps (config := { isSimp := false }) k] stopTM

/-- Relabelling the state keeps the work tapes (`Turing.Cfg.mapState_workTapes`, as functions). -/
private lemma mapState_workTapes_eq {k : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) : (c.mapState f).workTapes = c.workTapes := by
  funext i z
  rw [Cfg.mapState_workTapes]

/-- Relabelling the state keeps the work heads (`Turing.Cfg.mapState_workTapePos`, as functions). -/
private lemma mapState_workTapePos_eq {k : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) : (c.mapState f).workTapePos = c.workTapePos := by
  funext i
  rw [Cfg.mapState_workTapePos]

/-- Before the designated exit, the adapter takes the module's step and raises the release flag.

**Proof sketch.** `Cfg.mapState` keeps the tapes and heads, so the flagged configuration reads
the module's symbols, and the guard rules out the release branch: the adapter applies the
module's action with its successor state flagged `true`. -/
private lemma stopTM_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (stopTM C entry exit).tm.step (c.mapState (b, ·)) = (C.tm.step c).mapState (true, ·) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    have hsc : (c.mapState (b, ·)).state = some (b, q) := by
      rw [Cfg.mapState_state, hs, Option.map_some]
    rw [MultiTapeTM.step_of_some hsc, MultiTapeTM.step_of_some hs]
    have hin : (c.mapState (b, ·)).inputSymbol = c.inputSymbol :=
      Cfg.inputSymbol_congr _ _ (by rw [Cfg.mapState_inputPos])
    have hw : (c.mapState (b, ·)).workTapeSymbols = c.workTapeSymbols := by
      funext i
      rw [Cfg.workTapeSymbols_eq, Cfg.workTapeSymbols_eq, mapState_workTapes_eq,
        mapState_workTapePos_eq]
    rw [hin, hw]
    have htr : (stopTM C entry exit).tm.tr (b, q) c.inputSymbol c.workTapeSymbols =
        {C.tm.tr q c.inputSymbol c.workTapeSymbols with
          state := (C.tm.tr q c.inputSymbol c.workTapeSymbols).state.map (true, ·)} := by
      show (if (b, q).1 = true ∧ (b, q).2 = exit then _ else _) = _
      rw [if_neg hq]
    rw [htr]
    apply Cfg.ext
    · rw [Action.apply_state, Cfg.mapState_state, Action.apply_state]
    · rw [Action.apply_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos,
        Action.apply_inputPos]
    · funext i
      simp only [Action.apply_workTapes, mapState_workTapes_eq, mapState_workTapePos_eq, hw]
    · funext i
      simp only [Action.apply_workTapePos, mapState_workTapePos_eq]
    · rw [Action.apply_output, Cfg.mapState_output, Cfg.mapState_output, Action.apply_output]

/-- **The adapter stops a clean call**: if `C` runs from `entry` on the state word of `arg` and
returns to `exit` at a positive time `t`, without visiting `exit` at a positive time before `t`,
leaving the state word of `result` and output `out`, then the adapter, started in its start state
on the same word, halts at time `t + 1` with the state word of `result` and output `out`.

**Proof sketch.** Induct on the prefixes of the run: the adapter's configuration at time `v ≤ t`
is the module's with the flag `v ≠ 0` paired on (`stopTM_step`; the guard rules out an early
stop, and every earlier configuration is live because the endpoint is). At time `t` the flag is
raised and the state is `exit`, so the final transition halts silently and keeps every tape. -/
theorem stopTM_runFrom_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (stopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (stopTM C entry exit).tm.q₀
        (stateWord (stopTM C entry exit).k arg)) (t + 1) =
      {Cfg.ofWords (stopTM C entry exit).tm.q₀ (stateWord (stopTM C entry exit).k result) with
        state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hend : (C.tm.runFrom c t).state ≠ none := by
    rw [show C.tm.runFrom c t = _ from he]
    show (Cfg.ofWords (input := x) exit (stateWord C.k result)).state ≠ none
    rw [Cfg.ofWords_state]
    exact Option.some_ne_none _
  have hl := MultiTapeTM.runFrom_state_ne_none_of_le C.tm c t hend
  have hp : ∀ v, v ≤ t → (stopTM C entry exit).tm.runFrom (c.mapState (false, ·)) v =
      (C.tm.runFrom c v).mapState (decide (v ≠ 0), ·) := by
    intro v
    induction v with
    | zero =>
      intro _
      rw [MultiTapeTM.runFrom_zero, MultiTapeTM.runFrom_zero]
      simp
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        stopTM_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      simp
  have hi : Cfg.ofWords (input := x) (stopTM C entry exit).tm.q₀
      (stateWord (stopTM C entry exit).k arg) = c.mapState (false, ·) :=
    (Cfg.ofWords_mapState (fun s => (false, s)) entry (stateWord C.k arg)).symm
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _), hflag,
    show C.tm.runFrom c t = _ from he]
  -- the final transition: the flag is raised and the state is `exit`, so the adapter halts
  have hs : (({Cfg.ofWords exit (stateWord C.k result) with output := out} :
      Cfg C.k Bool C.State x).mapState (true, ·)).state = some (true, exit) := by
    simp only [Cfg.mapState_state, Cfg.ofWords_state, Option.map_some]
  rw [MultiTapeTM.step_of_some hs]
  have htr : ∀ inp work, (stopTM C entry exit).tm.tr (true, exit) inp work =
      FinTM.controlAction 0 none := by
    intro inp work
    show (if (true, exit).1 = true ∧ (true, exit).2 = exit then _ else _) = _
    rw [if_pos ⟨rfl, rfl⟩]
  rw [htr, FinTM.controlAction_def]
  apply Cfg.ext
  · rw [Action.apply_state]
  · simp only [Action.apply_inputPos, moveInputPos_zero, Cfg.mapState_inputPos,
      Cfg.ofWords_inputPos]
  · funext i
    simp only [Action.apply_workTapes, mapState_workTapes_eq, mapState_workTapePos_eq,
      Option.getD_none, Cfg.workTapeSymbols_eq, Function.update_eq_self, Cfg.ofWords_workTapes]
    rfl
  · funext i
    simp only [Action.apply_workTapePos, mapState_workTapePos_eq, SignType.coe_zero,
      Int.add_zero, Cfg.ofWords_workTapePos]
  · simp only [Action.apply_output, Cfg.mapState_output, Option.toList_none, List.append_nil]

/-- **A guarded positive return makes a clean module**: if `C` with a work tape has, from
`entry` on every state word `arg`, a positive return to `exit` within `B |arg|` that visits `exit`
at no earlier positive time and leaves the state word of `result arg` with output `emit arg`, then
the stop adapter is a clean module for `result` and `emit` with budget `B + 1`.

**Proof sketch.** `stopTM_runFrom_clean` halts the adapter at time `t + 1`; cut that run at its
first halt (`Turing.MultiTapeTM.exists_first_halt_pos`), which keeps the endpoint. -/
theorem CleanModule.of_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    CleanModule (stopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨by rw [stopTM_k]; exact hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := stopTM_runFrom_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := MultiTapeTM.exists_first_halt_pos
    (stopTM C entry exit).tm
    (Cfg.ofWords (input := x) (stopTM C entry exit).tm.q₀
      (stateWord (stopTM C entry exit).k arg)) (t + 1)
    (by rw [Cfg.ofWords_state]; exact Option.some_ne_none _) (by rw [hs])
  exact ⟨u, hu, by omega, hguard, hend.trans hs⟩

end FinTM

end Turing

namespace Complexity

open Turing

/-- The bridge overhead is bounded by one monomial of degree one higher.
**Proof sketch.** Output length is bounded by source time; `n + 1` and both source-time terms fit
the larger power. The last unit pays for stopping. -/
private lemma bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- A computed word is no longer than the computation's time bound. -/
private lemma output_le {F : FinTM Bool} {f : List Bool → List Bool} {A d : ℕ}
    (hF : F.ComputesFunInTime f fun n => A * (n + 1) ^ d) (arg : List Bool) :
    (f arg).length ≤ A * (arg.length + 1) ^ d := by
  have ho := ((FinTM.computesInTime_iff _ _ _ _).mp
    ((FinTM.computesFunInTime_iff _ _ _).mp hF arg)).2
  simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)

/-- A seam with an empty output, written with an explicit output update. -/
private lemma ofWords_with_output_nil {k : ℕ} {S : Type} {x : List Bool} (q : S)
    (w : Fin k → List Bool) :
    Cfg.ofWords (input := x) q w = {Cfg.ofWords (input := x) q w with output := []} :=
  Cfg.ext rfl rfl rfl rfl (Cfg.ofWords_output q w)

/-- A stopped clean-call bridge is a clean module with a polynomial budget: if `C` returns from
`entry` to `exit` within `c (A (n + 1)^d + n + |f arg| + 1)` steps, where `|f arg| ≤ A (n + 1)^d`,
then `stopTM C entry exit` is a clean module with budget `(c (2A + 1) + 1) (n + 1)^(d + 1)`. -/
private lemma clean_of_bridge (C : FinTM Bool) (entry exit : C.State)
    (f result emit : List Bool → List Bool) (c A d : ℕ) (hk : 0 < C.k)
    (hlen : ∀ arg, (f arg).length ≤ A * (arg.length + 1) ^ d)
    (hc : ∀ x arg : List Bool,
      ∃ t ≤ c * (A * (arg.length + 1) ^ d + arg.length + (f arg).length + 1), 0 < t ∧
        (∀ v, 0 < v → v < t → (C.tm.runFrom
          (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
        C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
          {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    FinTM.CleanModule (FinTM.stopTM C entry exit) result emit
      (fun n => (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1)) := by
  have hstop := FinTM.CleanModule.of_stop C entry exit result emit
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (fun x arg => by
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨hstop.pos, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.run x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- **Clean install modules**: every polynomial-time `f` has a clean module that replaces the
state word `arg` by `f arg` and emits nothing, within a polynomial budget in `|arg|`.

**Proof sketch.** Stop the install bridge `Turing.FinTM.exists_installCallTM`; the result length
is bounded by the source time, so the bridge's budget fits one monomial of degree one higher. -/
theorem exists_cleanInstall {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ (M : FinTM Bool) (A d : ℕ), FinTM.CleanModule M f (fun _ => [])
      (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := (polyTimeComputable_iff f).mp hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  refine ⟨_, _, _, clean_of_bridge C entry exit f f (fun _ => []) c A d hk (output_le hF)
    fun x arg => ?_⟩
  obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
  exact ⟨t, ht, hp, hg, he.trans (ofWords_with_output_nil _ _)⟩

/-- **Clean emit modules**: every polynomial-time `f` has a clean module that keeps the state
word `arg` and emits `f arg`, within a polynomial budget in `|arg|`.

**Proof sketch.** As `exists_cleanInstall`, from the emit bridge
`Turing.FinTM.exists_emitCallTM`. -/
theorem exists_cleanEmit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ (M : FinTM Bool) (A d : ℕ), FinTM.CleanModule M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := (polyTimeComputable_iff f).mp hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  refine ⟨_, _, _, clean_of_bridge C entry exit f id f c A d hk (output_le hF) fun x arg => ?_⟩
  obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
  exact ⟨t, ht, hp, hg, by rw [he, id_eq]⟩

end Complexity
