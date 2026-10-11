/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Running `Bool` machines on rich alphabets: the embedding transport

A machine over a rich work alphabet `Γ` often needs a binary routine (a counter, a
compare) on one of its tapes. Instead of re-proving each binary routine at `Γ`, this file
**lifts** a `Bool` machine along an embedding `e : Bool ↪ Γ`. The lifted machine reads
through `decodeBool e`, where foreign symbols read as blank, and writes and emits
through `e`. From every lifted configuration and at every time it runs as the original,
everything mapped along `e` (`Turing.MultiTapeTM.liftSymbols_runFrom`). It is the
embedding analogue of the equivalence transport `Turing.MultiTapeTM.mapWorkSymbols`
(`Build/CounterLoop.lean`). Space is preserved exactly. A lifted computation is a
computation *via* `e` in the sense `Turing.FinTM.alphabet_reduction` consumes, so a
rich-alphabet construction can finish by alphabet reduction.

Design: `machine-library-design.md` §12.8 (decision 12.8.1, rich-alphabet configuration
records) and §12.8a R8.0. Consumers: the §12.8 record rows, which run the binary counter
rows on dedicated digit tapes, and §13d's zone carrier, whose alphabet embeds `Bool` by
`Sum.inl`.

## Main definitions

* `Turing.decodeBool` — decoding along `e`; foreign symbols decode to `none`.
* `Turing.Action.liftSymbols`, `Turing.Cfg.liftSymbols`, `Turing.MultiTapeTM.liftSymbols`,
  `Turing.FinTM.liftSymbols` — the lift of actions, configurations and machines.

## Main results

* `Turing.MultiTapeTM.liftSymbols_runFrom` — the transport: lifted runs are lifts of runs.
* `Turing.MultiTapeTM.liftSymbols_step` — its one-step form.
* `Turing.MultiTapeTM.liftSymbols_initCfg`, `Turing.MultiTapeTM.liftSymbols_spaceUsed` — start
  configurations and space.
* `Turing.FinTM.liftSymbols_computesFunInTimeVia` — a lifted computation is a computation via
  `e`, in the same time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§1.2 and Claim 1.5: the alphabet of a machine can be changed at a
  constant-factor cost; this file is the cost-free direction, from `Bool` into a larger
  alphabet.)
-/

namespace Turing

section Lift
variable {k : ℕ} {Γ State : Type*}

/-- Decode a rich symbol along `e : Bool ↪ Γ`: `e b` decodes to `some b`, and every
symbol outside the image of `e` decodes to `none`, which the lifted machine reads as a
blank. -/
def decodeBool [DecidableEq Γ] (e : Bool ↪ Γ) (γ : Γ) : Option Bool :=
  if γ = e true then some true else if γ = e false then some false else none

/-- Decoding inverts `e` on its image.

**Proof sketch.** `cases b`; the two images differ by injectivity of `e`. -/
@[simp] lemma decodeBool_apply [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) :
    decodeBool e (e b) = some b := by
  cases b
  · have : e false ≠ e true := fun h => Bool.false_ne_true (e.injective h)
    simp [decodeBool, this]
  · simp [decodeBool]

/-- Lift an action along `e`: written symbols and the emission are mapped by `e`. -/
def Action.liftSymbols (e : Bool ↪ Γ) (a : Action k Bool State) : Action k Γ State where
  inputTape := a.inputTape
  workTapes := fun j => ((a.workTapes j).1.map (Option.map e), (a.workTapes j).2)
  output := a.output.map e
  state := a.state

/-- Lift a configuration along `e`: input, work cells and output mapped by `e`. -/
def Cfg.liftSymbols (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) :
    Cfg k Γ State (x.map e) where
  state := c.state
  inputPos := Fin.cast (by simp) c.inputPos
  workTapes := fun j p => (c.workTapes j p).map e
  workTapePos := c.workTapePos
  output := c.output.map e

/-- Lift a machine along `e`: read through `decodeBool e`, write through `e`. -/
def MultiTapeTM.liftSymbols [DecidableEq Γ] (M : MultiTapeTM k Bool State) (e : Bool ↪ Γ) :
    MultiTapeTM k Γ State where
  q₀ := M.q₀
  tr := fun q inp work =>
    (M.tr q (inp.bind (decodeBool e)) fun j => (work j).bind (decodeBool e)).liftSymbols e

/-- The lifted configuration reads the mapped input symbol.

**Proof sketch.** The two input positions have the same value, so the end-marker cases
match; an inner position reads `(x.map e)[i] = e x[i]`. -/
lemma Cfg.liftSymbols_inputSymbol (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) :
    (c.liftSymbols e).inputSymbol = c.inputSymbol.map e := by
  have hv : ((c.liftSymbols e).inputPos : ℕ) = c.inputPos := rfl
  unfold Cfg.inputSymbol
  have e0 : ((c.liftSymbols e).inputPos = 0) ↔ (c.inputPos = 0) := by
    simp only [Fin.ext_iff, hv, Fin.val_zero]
  have e1 : ((c.liftSymbols e).inputPos = ((x.map e).length + 1 : ℕ)) ↔
      (c.inputPos = (x.length + 1 : ℕ)) := by
    simp only [hv, List.length_map]
  by_cases h0 : c.inputPos = 0
  · rw [dif_pos (e0.mpr h0), dif_pos h0]; rfl
  · rw [dif_neg (fun h => h0 (e0.mp h)), dif_neg h0]
    by_cases h1 : c.inputPos = (x.length + 1 : ℕ)
    · rw [dif_pos (e1.mpr h1), dif_pos h1]; rfl
    · rw [dif_neg (fun h => h1 (e1.mp h)), dif_neg h1]
      simp [hv]

/-- Moving the input head commutes with recasting the position type. -/
private lemma moveInputPos_cast {n m : ℕ} (h : n + 2 = m + 2) (p : Fin (n + 2)) (s : SignType) :
    moveInputPos (Fin.cast h p) s = Fin.cast h (moveInputPos p s) := by
  have hnm : n = m := by omega
  subst hnm
  rfl

/-- One step commutes with the lift.

**Proof sketch.** A halted configuration does not move. Otherwise the lifted machine
decodes the scanned symbols back to the original ones (`decodeBool_apply`), so it
selects the lift of the original action; applying a lifted action to a lifted
configuration is the lift of the applied action, cell by cell. -/
lemma MultiTapeTM.liftSymbols_step [DecidableEq Γ] (M : MultiTapeTM k Bool State)
    (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) :
    (M.liftSymbols e).step (c.liftSymbols e) = (M.step c).liftSymbols e := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.liftSymbols, hs]
  | some q =>
    have hin : (c.liftSymbols e).inputSymbol.bind (decodeBool e) = c.inputSymbol := by
      rw [Cfg.liftSymbols_inputSymbol]; cases c.inputSymbol <;> simp
    have hw : (fun j => ((c.liftSymbols e).workTapeSymbols j).bind (decodeBool e)) =
        c.workTapeSymbols := by
      funext j; simp only [Cfg.workTapeSymbols, Cfg.liftSymbols]
      cases c.workTapes j (c.workTapePos j) <;> simp
    simp only [MultiTapeTM.step,
      show (c.liftSymbols e).state = some q by simp [Cfg.liftSymbols, hs], hs]
    change ((M.tr q ((c.liftSymbols e).inputSymbol.bind (decodeBool e))
      fun j => ((c.liftSymbols e).workTapeSymbols j).bind (decodeBool e)).liftSymbols e).apply
        (c.liftSymbols e) = _
    rw [hin, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_cast (by simp) _ _
    · funext j p
      simp only [Action.apply, Action.liftSymbols, Cfg.liftSymbols]
      cases (M.tr q c.inputSymbol c.workTapeSymbols).workTapes j |>.1 with
      | none => simp
      | some v =>
        simp only [Option.map_some]
        by_cases hp : p = c.workTapePos j
        · subst p; simp
        · simp [Function.update_of_ne hp]
    · rfl
    · simp only [Action.apply, Action.liftSymbols, Cfg.liftSymbols, List.map_append]
      cases (M.tr q c.inputSymbol c.workTapeSymbols).output <;> rfl

/-- **The embedding transport** (§12.8 R8.0): from every `Bool` configuration and at
every time, the lifted machine runs as the original, with input, work cells and output
mapped along `e`.

**Proof sketch.** Induction on `t` with `liftSymbols_step`. -/
theorem MultiTapeTM.liftSymbols_runFrom [DecidableEq Γ] (M : MultiTapeTM k Bool State)
    (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).runFrom (c.liftSymbols e) t = (M.runFrom c t).liftSymbols e := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.liftSymbols_step, ih]

/-- The lift keeps the state. -/
@[simp] lemma Cfg.liftSymbols_state (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) :
    (c.liftSymbols e).state = c.state := rfl

/-- The lift keeps the work-head positions. -/
@[simp] lemma Cfg.liftSymbols_workTapePos (e : Bool ↪ Γ) {x : List Bool}
    (c : Cfg k Bool State x) : (c.liftSymbols e).workTapePos = c.workTapePos := rfl

/-- The lifted machine starts at the lift of the original start (both blank tapes, same
heads and state). -/
lemma MultiTapeTM.liftSymbols_initCfg [DecidableEq Γ] (M : MultiTapeTM k Bool State)
    (e : Bool ↪ Γ) (x : List Bool) :
    (M.liftSymbols e).initCfg (x.map e) = (M.initCfg x).liftSymbols e := by
  apply Cfg.ext <;> rfl

/-- Space is preserved exactly: the head trajectories are the same.

**Proof sketch.** Unfold the visited sets and rewrite with `liftSymbols_runFrom`. -/
lemma MultiTapeTM.liftSymbols_spaceUsed [DecidableEq Γ] (M : MultiTapeTM k Bool State)
    (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).spaceUsed (c.liftSymbols e) t = M.spaceUsed c t := by
  simp [MultiTapeTM.spaceUsed, MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead,
    MultiTapeTM.liftSymbols_runFrom]

end Lift

/-- The `FinTM` layer of the lift. -/
def FinTM.liftSymbols {Γ : Type} [DecidableEq Γ] (M : FinTM Bool) (e : Bool ↪ Γ) : FinTM Γ :=
  ⟨M.k, M.State, M.tm.liftSymbols e⟩

/-- A `Bool` machine computing `f` computes `f` via `e` when lifted, in the same time:
the form `Turing.FinTM.alphabet_reduction` consumes.

**Proof sketch.** Rewrite the lifted run from the lifted start with
`liftSymbols_initCfg` and `liftSymbols_runFrom`; halting and the mapped output follow. -/
theorem FinTM.liftSymbols_computesFunInTimeVia {Γ : Type} [DecidableEq Γ] (M : FinTM Bool)
    (e : Bool ↪ Γ) {f : List Bool → List Bool} {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) :
    (M.liftSymbols e).ComputesFunInTimeVia e f T := by
  intro x
  have hx := (FinTM.computesInTime_iff _ _ _ _).mp (h x)
  refine (FinTM.computesInTime_iff _ _ _ _).mpr ?_
  change ((M.tm.liftSymbols e).runFrom ((M.tm.liftSymbols e).initCfg (x.map e)) _).state = none ∧
    ((M.tm.liftSymbols e).runFrom ((M.tm.liftSymbols e).initCfg (x.map e)) _).output = _
  rw [MultiTapeTM.liftSymbols_initCfg, MultiTapeTM.liftSymbols_runFrom]
  exact ⟨hx.1, congrArg (List.map e) hx.2⟩

end Turing
