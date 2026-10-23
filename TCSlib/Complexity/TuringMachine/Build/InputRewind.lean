/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The input rewind as a machine

A small machine that returns the native input head to the first input cell: one step left, then
left while the head reads an input symbol, then one step right at the left blank, into a
stationary live state. From any configuration whose input head is at position `p ≥ 1`, it reaches
its last state at exactly time `p + 1`, not earlier, with the input head at `1`, and leaves every
work tape, every work head and the output unchanged at every time. A machine that rewinds its
input in one phase of a composite uses it as that phase.

Also, the composition of two state relabelings of a configuration is one relabeling.

## Main definitions

* `Turing.InputRewindPhase` — the rewind's three control states.
* `Turing.inputRewindTM` — the rewind over any number of work tapes.

## Main results

* `Turing.inputRewindTM_run` — the exact time, the first arrival at the last state, the
  endpoint, and the unchanged work tapes, heads and output.
* `Turing.inputRewindTM_step_done` — the last state is a stationary park.
* `Turing.Cfg.mapState_mapState` — relabeling twice is relabeling by the composite.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the input head and its moves.)
-/

namespace Turing

/-- **Relabeling twice is relabeling once**: renaming a configuration's states by `f` and then
by `g` renames them by `g ∘ f`.

**Proof sketch.** Compare the five fields through `Turing.Cfg.mapState`'s field equations; the
state is `Option.map_map`. -/
theorem Cfg.mapState_mapState {k : ℕ} {Symbol : Type*} {S₁ S₂ S₃ : Type*} {x : List Symbol}
    (c : Cfg k Symbol S₁ x) (f : S₁ → S₂) (g : S₂ → S₃) :
    (c.mapState f).mapState g = c.mapState (g ∘ f) := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, Option.map_map]
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext i q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext i
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]

/-- The input rewind's control states: the first left step, the scan, and the park. -/
inductive InputRewindPhase where
  /-- the first, unconditional left step -/
  | start
  /-- the scan left over the input symbols -/
  | scan
  /-- the stationary live park, reached with the input head at `1` -/
  | done
  deriving DecidableEq, Fintype

/-- **The input rewind**: one step left, then left while the input head reads a symbol, then one
step right at the left blank into the park, which stays put. It never writes, moves a work head or
emits. -/
def inputRewindTM (k : ℕ) : MultiTapeTM k Bool InputRewindPhase where
  q₀ := .start
  tr := fun q inp _ =>
    match q with
    | .start => FinTM.controlAction .neg (some .scan)
    | .scan =>
      match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos (some .done)
    | .done => FinTM.controlAction 0 (some .done)

/-- **The input rewind's run**: from a configuration in `start` whose input head is at
`p ≥ 1`, the machine is at `done` at exactly time `p + 1` and not earlier, with the input head at
`1` and everything else as it was; at every time up to then, its work tapes, work heads and output
are the start's.

**Proof sketch.** At time `r ≤ p` the configuration is the start's with the input head at
`p - r` (in `scan` for `r ≥ 1`): each step reads an input symbol, since the head is at a positive
position, and moves left (`Turing.FinTM.controlAction_apply`). At time `p` the head is on the left
blank, and one step right enters `done` at position `1`. -/
theorem inputRewindTM_run {k : ℕ} {x : List Bool} (d : Cfg k Bool InputRewindPhase x)
    (hstate : d.state = some .start) (hp : 1 ≤ d.inputPos.val) :
    (inputRewindTM k).runFrom d (d.inputPos.val + 1) =
        { d with state := some .done, inputPos := 1 } ∧
      (∀ t < d.inputPos.val + 1, ((inputRewindTM k).runFrom d t).state ≠ some .done) ∧
      ∀ t ≤ d.inputPos.val + 1,
        ((inputRewindTM k).runFrom d t).workTapes = d.workTapes ∧
        ((inputRewindTM k).runFrom d t).workTapePos = d.workTapePos ∧
        ((inputRewindTM k).runFrom d t).output = d.output := by
  classical
  have hlt := d.inputPos.isLt
  -- the scan's trajectory
  let T : ℕ → Cfg k Bool InputRewindPhase x := fun r =>
    { d with
      state := some (if r = 0 then .start else .scan)
      inputPos := ⟨d.inputPos.val - r, by omega⟩ }
  have hT0 : T 0 = d := by
    refine Cfg.ext ?_ ?_ rfl rfl rfl
    · show some (if 0 = 0 then InputRewindPhase.start else .scan) = d.state
      rw [if_pos rfl, hstate]
    · refine Fin.ext ?_
      show d.inputPos.val - 0 = d.inputPos.val
      omega
  have hstep : ∀ r : ℕ, r ≤ d.inputPos.val - 1 → (inputRewindTM k).step (T r) = T (r + 1) := by
    intro r hr
    have hs : (T r).state = some (if r = 0 then .start else .scan) := rfl
    rw [MultiTapeTM.step_of_some hs]
    have htr : (inputRewindTM k).tr (if r = 0 then .start else .scan) (T r).inputSymbol
        (T r).workTapeSymbols = FinTM.controlAction .neg (some .scan) := by
      by_cases hr0 : r = 0
      · rw [if_pos hr0]
        rfl
      · rw [if_neg hr0]
        have hread : (T r).inputSymbol = some (x[d.inputPos.val - r - 1]'(by omega)) := by
          refine inputSymbolInner (d.inputPos.val - r - 1) ?_ (by omega)
          show d.inputPos.val - r = 1 + (d.inputPos.val - r - 1)
          omega
        rw [hread]
        rfl
    rw [htr, FinTM.controlAction_apply]
    refine Cfg.ext ?_ ?_ rfl rfl rfl
    · show some InputRewindPhase.scan = some (if r + 1 = 0 then .start else .scan)
      rw [if_neg (Nat.succ_ne_zero r)]
    · show moveInputPos (T r).inputPos .neg = (T (r + 1)).inputPos
      rw [moveInputPos_neg_of_ne_left _ (by
        intro h
        have hv : d.inputPos.val - r = 0 := by
          have hvv := congrArg Fin.val h
          simpa [T] using hvv
        omega)]
      exact Fin.ext (by show d.inputPos.val - r - 1 = d.inputPos.val - (r + 1); omega)
  have hrun : ∀ r : ℕ, r ≤ d.inputPos.val → (inputRewindTM k).runFrom d r = T r := by
    intro r hr
    induction r with
    | zero => rw [MultiTapeTM.runFrom_zero, hT0]
    | succ r ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep r (by omega)]
  have hfinal : (inputRewindTM k).step (T d.inputPos.val) =
      { d with state := some .done, inputPos := 1 } := by
    have hs : (T d.inputPos.val).state = some .scan := by
      show some (if d.inputPos.val = 0 then InputRewindPhase.start else .scan) = some .scan
      rw [if_neg (by omega)]
    rw [MultiTapeTM.step_of_some hs]
    have hzero : (T d.inputPos.val).inputPos = 0 := by
      refine Fin.ext ?_
      show d.inputPos.val - d.inputPos.val = (0 : Fin (x.length + 2)).val
      rw [Fin.val_zero]
      omega
    have hread : (T d.inputPos.val).inputSymbol = none := Cfg.inputSymbol_of_zero hzero
    have htr : (inputRewindTM k).tr .scan (T d.inputPos.val).inputSymbol
        (T d.inputPos.val).workTapeSymbols = FinTM.controlAction .pos (some .done) := by
      rw [hread]
      rfl
    rw [htr, FinTM.controlAction_apply]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    show moveInputPos (T d.inputPos.val).inputPos .pos = (1 : Fin (x.length + 2))
    rw [hzero, moveInputPos_pos_of_ne_right (0 : Fin (x.length + 2))
      (by rw [Fin.val_zero]; omega)]
    exact Fin.ext (by simp)
  have hend : (inputRewindTM k).runFrom d (d.inputPos.val + 1) =
      { d with state := some .done, inputPos := 1 } := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hrun d.inputPos.val le_rfl, hfinal]
  refine ⟨hend, ?_, ?_⟩
  · intro t ht
    rw [hrun t (by omega)]
    show some (if t = 0 then InputRewindPhase.start else .scan) ≠ some .done
    by_cases ht0 : t = 0
    · rw [if_pos ht0]; decide
    · rw [if_neg ht0]; decide
  · intro t ht
    rcases Nat.lt_or_ge t (d.inputPos.val + 1) with hlt' | hge
    · rw [hrun t (by omega)]
      exact ⟨rfl, rfl, rfl⟩
    · rw [show t = d.inputPos.val + 1 by omega, hend]
      exact ⟨rfl, rfl, rfl⟩

/-- **The park stays put**: at `done` the rewind's step changes nothing. -/
theorem inputRewindTM_step_done {k : ℕ} {x : List Bool} (c : Cfg k Bool InputRewindPhase x)
    (hc : c.state = some .done) : (inputRewindTM k).step c = c := by
  rw [MultiTapeTM.step_of_some hc]
  show (FinTM.controlAction 0 (some InputRewindPhase.done)).apply c = c
  rw [FinTM.controlAction_apply]
  refine Cfg.ext ?_ ?_ rfl rfl rfl
  · rw [hc]
  · exact moveInputPos_zero c.inputPos

end Turing
