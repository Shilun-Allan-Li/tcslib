/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Nondeterministic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic machines: locality, output maps and the coin dispatcher

Generic run lemmas and two small combinators for binary-choice machines `Turing.NDTM`, the
nondeterministic counterpart of the deterministic construction layer (which has no NDTM rows).
They serve the clocked restart host `Turing.FinNDTM.clockHost`
(`TCSlib.Complexity.TuringMachine.Build.NDClockHost`) and the zero-error constructions of
[AB09, §7.3] (`TCSlib.Complexity.Randomized.ZPPHosts`).

## Main definitions

* `Turing.NDTM.AgreeShift` — two configurations agree up to a translation of the work tapes, on
  the cells at or right of `head - r`.
* `Turing.NDTM.mapOutput`, `Turing.FinNDTM.mapOutput` — replace every emitted symbol `s` by
  `f s : Option _`.
* `Turing.FinNDTM.coinBranch` — read one coin and run one of two machines on its own bank.

## Main results

* `Turing.NDTM.AgreeShift.runWith` — a run of `t` steps only reads cells within distance `t`
  of the heads, and commutes with translating the tapes.
* `Turing.NDTM.abs_runWith_workTapePos_sub_le`, `Turing.NDTM.runWith_workTapes_of_le` — heads
  move at most one cell per step, and cells beyond reach are not written.
* `Turing.NDTM.mapOutput_runWith`, `Turing.FinNDTM.coinBranch_runWith` — the run of each
  combinator is the run of its source.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing

/-- A head move is at most one cell. -/
private theorem signType_bounds (s : SignType) : -1 ≤ (s : ℤ) ∧ (s : ℤ) ≤ 1 := by
  cases s <;> simp

namespace NDTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A live step applies the action selected by the coin. -/
theorem stepWith_of_state (tm : NDTM k Symbol State) (b : Bool) {c : Cfg k Symbol State input}
    {q : State} (h : c.state = some q) :
    tm.stepWith b c = (tm.tr b q c.inputSymbol c.workTapeSymbols).apply c := by
  unfold stepWith
  rw [h]

/-! ### Translation and locality -/

/-- `c'` is `c` translated by `d` on the work tapes, as far as the cells at or right of
`head - r` go: same state, input head and output, heads shifted by `d`, and
`c'.tape i (z + d i) = c.tape i z` for `z ≥ c.head i - r`. -/
def AgreeShift (r : ℕ) (d : Fin k → ℤ) (c c' : Cfg k Symbol State input) : Prop :=
  c'.state = c.state ∧ c'.inputPos = c.inputPos ∧ c'.output = c.output ∧
    (∀ i, c'.workTapePos i = c.workTapePos i + d i) ∧
    ∀ i z, c.workTapePos i - r ≤ z → c'.workTapes i (z + d i) = c.workTapes i z

/-- One step preserves `AgreeShift`, shrinking the window by one cell.

**Proof sketch.** A halted step changes nothing. Otherwise the two machines read the same
symbols (the heads lie in the window), so they apply the same action; the written cell is the
head in both, and every other cell of the shrunken window was in the old one. -/
theorem AgreeShift.stepWith (tm : NDTM k Symbol State) (b : Bool) {r : ℕ} {d : Fin k → ℤ}
    {c c' : Cfg k Symbol State input} (h : AgreeShift (r + 1) d c c') :
    AgreeShift r d (tm.stepWith b c) (tm.stepWith b c') := by
  obtain ⟨hs, hi, ho, hp, ht⟩ := h
  cases hq : c.state with
  | none =>
    rw [stepWith_of_halt hq, stepWith_of_halt (hs.trans hq)]
    exact ⟨hs, hi, ho, hp, fun i z hz => ht i z (by push_cast at hz ⊢; omega)⟩
  | some q =>
    have hq' : c'.state = some q := hs.trans hq
    have hsym : c'.workTapeSymbols = c.workTapeSymbols := funext fun i => by
      simp only [Cfg.workTapeSymbols, hp]
      exact ht i _ (by omega)
    have hin : c'.inputSymbol = c.inputSymbol := by simp only [Cfg.inputSymbol, hi]
    simp only [NDTM.stepWith, hq, hq', hsym, hin]
    refine ⟨rfl, by simp [Action.apply, hi], by simp [Action.apply, ho],
      fun i => by simp only [Action.apply, hp]; omega, fun i z hz => ?_⟩
    have hb := signType_bounds
      ((tm.tr b q c.inputSymbol c.workTapeSymbols).workTapes i).2
    simp only [Action.apply] at hz ⊢
    have hz' : c.workTapePos i - ((r + 1 : ℕ) : ℤ) ≤ z := by push_cast; omega
    cases ((tm.tr b q c.inputSymbol c.workTapeSymbols).workTapes i).1 with
    | none => exact ht i z hz'
    | some s =>
      dsimp only
      rw [hp, Function.update_apply, Function.update_apply]
      by_cases hzc : z = c.workTapePos i
      · subst hzc; simp
      · rw [if_neg (by omega), if_neg hzc]
        exact ht i z hz'

/-- `AgreeShift` over a run: a run of `|w|` steps reads no cell left of `head - |w|`, and
commutes with translation. -/
theorem AgreeShift.runWith (tm : NDTM k Symbol State) (w : List Bool) {r : ℕ}
    {d : Fin k → ℤ} {c c' : Cfg k Symbol State input} (h : AgreeShift (r + w.length) d c c') :
    AgreeShift r d (tm.runWith w c) (tm.runWith w c') := by
  induction w generalizing c c' with
  | nil => exact h
  | cons b w ih =>
    rw [runWith_cons, runWith_cons]
    refine ih (AgreeShift.stepWith tm b ?_)
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h

/-- A configuration agrees with itself, untranslated, on every window. -/
theorem AgreeShift.refl (r : ℕ) (c : Cfg k Symbol State input) :
    AgreeShift r (fun _ => 0) c c :=
  ⟨rfl, rfl, rfl, fun _ => by simp, fun _ _ _ => by simp⟩

/-- Each work head moves at most `|w|` cells during a run of `|w|` steps. -/
theorem abs_runWith_workTapePos_sub_le (tm : NDTM k Symbol State) (w : List Bool)
    (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.runWith w c).workTapePos i - c.workTapePos i| ≤ w.length := by
  induction w generalizing c with
  | nil => simp
  | cons b w ih =>
    rw [runWith_cons]
    have h1 := ih (tm.stepWith b c)
    have h2 : |(tm.stepWith b c).workTapePos i - c.workTapePos i| ≤ 1 := by
      cases hq : c.state with
      | none => rw [stepWith_of_halt hq]; simp
      | some q =>
        rw [stepWith_of_state tm b hq]
        simp only [Action.apply, add_sub_cancel_left]
        have := signType_bounds ((tm.tr b q c.inputSymbol c.workTapeSymbols).workTapes i).2
        rw [abs_le]; omega
    rw [abs_le] at h1 h2 ⊢
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    omega

/-- A run of `|w|` steps does not write any cell at distance `≥ |w|` to the right of the
starting head. -/
theorem runWith_workTapes_of_le (tm : NDTM k Symbol State) (w : List Bool)
    (c : Cfg k Symbol State input) (i : Fin k) (z : ℤ) (hz : c.workTapePos i + w.length ≤ z) :
    (tm.runWith w c).workTapes i z = c.workTapes i z := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih =>
    rw [runWith_cons]
    have hmove := abs_runWith_workTapePos_sub_le tm [b] c i
    simp only [runWith_cons, runWith_nil, List.length_singleton, Nat.cast_one] at hmove
    rw [abs_le] at hmove
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hz
    rw [ih (tm.stepWith b c) (by omega)]
    cases hq : c.state with
    | none => rw [stepWith_of_halt hq]
    | some q =>
      rw [stepWith_of_state tm b hq]
      simp only [Action.apply]
      cases ((tm.tr b q c.inputSymbol c.workTapeSymbols).workTapes i).1 with
      | none => rfl
      | some s => dsimp only; rw [Function.update_apply, if_neg (by omega)]

/-! ### Output maps -/

/-- The machine `tm` with every emitted symbol `s` replaced by `f s` (nothing if `none`). -/
def mapOutput (tm : NDTM k Symbol State) (f : Symbol → Option Symbol) : NDTM k Symbol State :=
  ⟨tm.q₀, fun b q i w => { tm.tr b q i w with output := (tm.tr b q i w).output.bind f }⟩

/-- A configuration with its output tape filtered through `f`. -/
def mapOutputCfg (f : Symbol → Option Symbol) (c : Cfg k Symbol State input) :
    Cfg k Symbol State input :=
  { c with output := c.output.filterMap f }

/-- One step of `mapOutput` on a filtered configuration is the filtered step. -/
theorem mapOutput_stepWith (tm : NDTM k Symbol State) (f : Symbol → Option Symbol) (b : Bool)
    (c : Cfg k Symbol State input) :
    (tm.mapOutput f).stepWith b (mapOutputCfg f c) = mapOutputCfg f (tm.stepWith b c) := by
  cases h : c.state with
  | none =>
    rw [stepWith_of_halt h, stepWith_of_halt (by simpa [mapOutputCfg] using h)]
  | some q =>
    have h' : (mapOutputCfg f c).state = some q := by simpa [mapOutputCfg] using h
    have hi : (mapOutputCfg f c).inputSymbol = c.inputSymbol := rfl
    have hw : (mapOutputCfg f c).workTapeSymbols = c.workTapeSymbols := rfl
    simp only [NDTM.stepWith, h, h', hi, hw]
    refine Cfg.ext rfl rfl rfl rfl ?_
    simp only [mapOutput, mapOutputCfg, Action.apply, List.filterMap_append]
    cases (tm.tr b q c.inputSymbol c.workTapeSymbols).output with
    | none => simp
    | some v => cases hv : f v <;> simp [hv]

/-- Running `mapOutput` from a filtered configuration gives the filtered run. -/
theorem mapOutput_runWith (tm : NDTM k Symbol State) (f : Symbol → Option Symbol)
    (w : List Bool) (c : Cfg k Symbol State input) :
    (tm.mapOutput f).runWith w (mapOutputCfg f c) = mapOutputCfg f (tm.runWith w c) := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, runWith_cons, mapOutput_stepWith, ih]

/-- `mapOutput` starts in the filtered initial configuration. -/
theorem mapOutput_initCfg (tm : NDTM k Symbol State) (f : Symbol → Option Symbol)
    (x : List Symbol) : (tm.mapOutput f).initCfg x = mapOutputCfg f (tm.initCfg x) := rfl

end NDTM

/-! ### The coin dispatcher -/

namespace FinNDTM

/-- `NDTM.mapOutput` on the bundled layer. -/
def mapOutput (N : FinNDTM Bool) (f : Bool → Option Bool) : FinNDTM Bool :=
  ⟨N.k, N.State, N.tm.mapOutput f⟩

variable (N₀ N₁ : FinNDTM Bool)

/-- Embed an action of `N₀` into the dispatcher: `N₀`'s tapes are the first bank. -/
def coinBranchAct₀ (a : Action N₀.k Bool N₀.State) :
    Action (N₀.k + N₁.k) Bool (Option (N₀.State ⊕ N₁.State)) :=
  ⟨a.inputTape, Fin.append a.workTapes fun _ => (none, 0), a.output, a.state.map (some ∘ Sum.inl)⟩

/-- Embed an action of `N₁` into the dispatcher: `N₁`'s tapes are the second bank. -/
def coinBranchAct₁ (a : Action N₁.k Bool N₁.State) :
    Action (N₀.k + N₁.k) Bool (Option (N₀.State ⊕ N₁.State)) :=
  ⟨a.inputTape, Fin.append (fun _ => (none, 0)) a.workTapes, a.output, a.state.map (some ∘ Sum.inr)⟩

/-- **The coin dispatcher**: read one coin `b`, then run `N₀` (on `b = false`) or `N₁`
(on `b = true`), each on its own bank of work tapes. -/
def coinBranch : FinNDTM Bool :=
  @FinNDTM.mk Bool (N₀.k + N₁.k) (Option (N₀.State ⊕ N₁.State))
    inferInstance inferInstance
    { q₀ := none
      tr := fun b q i w => match q with
        | none => ⟨0, fun _ => (none, 0), none,
            some (some (if b then Sum.inr N₁.tm.q₀ else Sum.inl N₀.tm.q₀))⟩
        | some (.inl q) => coinBranchAct₀ N₀ N₁ (N₀.tm.tr b q i fun j => w (Fin.castAdd N₁.k j))
        | some (.inr q) => coinBranchAct₁ N₀ N₁ (N₁.tm.tr b q i fun j => w (Fin.natAdd N₀.k j)) }

variable {x : List Bool}

/-- A configuration of `N₀` inside the dispatcher, with the second bank blank. -/
def coinBranchCfg₀ (c : Cfg N₀.k Bool N₀.State x) : Cfg (coinBranch N₀ N₁).k Bool
    (coinBranch N₀ N₁).State x :=
  ⟨c.state.map (some ∘ Sum.inl), c.inputPos, Fin.append c.workTapes fun _ _ => none,
    Fin.append c.workTapePos fun _ => 0, c.output⟩

/-- A configuration of `N₁` inside the dispatcher, with the first bank blank. -/
def coinBranchCfg₁ (c : Cfg N₁.k Bool N₁.State x) : Cfg (coinBranch N₀ N₁).k Bool
    (coinBranch N₀ N₁).State x :=
  ⟨c.state.map (some ∘ Sum.inr), c.inputPos, Fin.append (fun _ _ => none) c.workTapes,
    Fin.append (fun _ => 0) c.workTapePos, c.output⟩

/-- One dispatcher step on an embedded `N₀` configuration is an `N₀` step.

**Proof sketch.** The dispatcher's action at an `N₀` state is `N₀`'s action on the first bank,
idle on the second; compare the two banks tape by tape (`Fin.addCases`). The `N₁` case is
symmetric. -/
theorem coinBranch_stepWith₀ (b : Bool) (c : Cfg N₀.k Bool N₀.State x) :
    (coinBranch N₀ N₁).tm.stepWith b (coinBranchCfg₀ N₀ N₁ c) =
      coinBranchCfg₀ N₀ N₁ (N₀.tm.stepWith b c) := by
  cases hq : c.state with
  | none =>
    rw [NDTM.stepWith_of_halt hq, NDTM.stepWith_of_halt (by simp [coinBranchCfg₀, hq])]
  | some q =>
    have hq' : (coinBranchCfg₀ N₀ N₁ c).state = some (some (Sum.inl q)) := by
      simp [coinBranchCfg₀, hq]
    have hw : (fun j => (coinBranchCfg₀ N₀ N₁ c).workTapeSymbols (Fin.castAdd N₁.k j)) =
        c.workTapeSymbols := funext fun j => by
      simp [coinBranchCfg₀, Cfg.workTapeSymbols]
    have hi : (coinBranchCfg₀ N₀ N₁ c).inputSymbol = c.inputSymbol := rfl
    rw [NDTM.stepWith_of_state _ b hq', NDTM.stepWith_of_state _ b hq]
    change (coinBranchAct₀ N₀ N₁ (N₀.tm.tr b q (coinBranchCfg₀ N₀ N₁ c).inputSymbol fun j =>
      (coinBranchCfg₀ N₀ N₁ c).workTapeSymbols (Fin.castAdd N₁.k j))).apply _ = _
    rw [hw, hi]
    refine Cfg.ext ?_ rfl ?_ ?_ rfl
    · simp [coinBranchAct₀, coinBranchCfg₀]
    · funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Action.apply, coinBranchAct₀, coinBranchCfg₀, Fin.append_left]
      · simp [Action.apply, coinBranchAct₀, coinBranchCfg₀]
    · funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [Action.apply, coinBranchAct₀, coinBranchCfg₀]

/-- One dispatcher step on an embedded `N₁` configuration is an `N₁` step.

**Proof sketch.** Symmetric to `coinBranch_stepWith₀`, on the second bank. -/
theorem coinBranch_stepWith₁ (b : Bool) (c : Cfg N₁.k Bool N₁.State x) :
    (coinBranch N₀ N₁).tm.stepWith b (coinBranchCfg₁ N₀ N₁ c) =
      coinBranchCfg₁ N₀ N₁ (N₁.tm.stepWith b c) := by
  cases hq : c.state with
  | none =>
    rw [NDTM.stepWith_of_halt hq, NDTM.stepWith_of_halt (by simp [coinBranchCfg₁, hq])]
  | some q =>
    have hq' : (coinBranchCfg₁ N₀ N₁ c).state = some (some (Sum.inr q)) := by
      simp [coinBranchCfg₁, hq]
    have hw : (fun j => (coinBranchCfg₁ N₀ N₁ c).workTapeSymbols (Fin.natAdd N₀.k j)) =
        c.workTapeSymbols := funext fun j => by
      simp [coinBranchCfg₁, Cfg.workTapeSymbols]
    have hi : (coinBranchCfg₁ N₀ N₁ c).inputSymbol = c.inputSymbol := rfl
    rw [NDTM.stepWith_of_state _ b hq', NDTM.stepWith_of_state _ b hq]
    change (coinBranchAct₁ N₀ N₁ (N₁.tm.tr b q (coinBranchCfg₁ N₀ N₁ c).inputSymbol fun j =>
      (coinBranchCfg₁ N₀ N₁ c).workTapeSymbols (Fin.natAdd N₀.k j))).apply _ = _
    rw [hw, hi]
    refine Cfg.ext ?_ rfl ?_ ?_ rfl
    · simp [coinBranchAct₁, coinBranchCfg₁]
    · funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [Action.apply, coinBranchAct₁, coinBranchCfg₁]
      · simp only [Action.apply, coinBranchAct₁, coinBranchCfg₁, Fin.append_right]
    · funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [Action.apply, coinBranchAct₁, coinBranchCfg₁]

/-- Runs of `N₀` lift to the dispatcher. -/
theorem coinBranch_runWith₀ (w : List Bool) (c : Cfg N₀.k Bool N₀.State x) :
    (coinBranch N₀ N₁).tm.runWith w (coinBranchCfg₀ N₀ N₁ c) =
      coinBranchCfg₀ N₀ N₁ (N₀.tm.runWith w c) := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih => rw [NDTM.runWith_cons, NDTM.runWith_cons, coinBranch_stepWith₀, ih]

/-- Runs of `N₁` lift to the dispatcher. -/
theorem coinBranch_runWith₁ (w : List Bool) (c : Cfg N₁.k Bool N₁.State x) :
    (coinBranch N₀ N₁).tm.runWith w (coinBranchCfg₁ N₀ N₁ c) =
      coinBranchCfg₁ N₀ N₁ (N₁.tm.runWith w c) := by
  induction w generalizing c with
  | nil => rfl
  | cons b w ih => rw [NDTM.runWith_cons, NDTM.runWith_cons, coinBranch_stepWith₁, ih]

/-- The dispatcher's first step reads the coin and enters the chosen machine's start.

**Proof sketch.** Both sides are blank configurations; compare field by field. -/
theorem coinBranch_stepWith_init (b : Bool) :
    (coinBranch N₀ N₁).tm.stepWith b ((coinBranch N₀ N₁).tm.initCfg x) =
      if b then coinBranchCfg₁ N₀ N₁ (N₁.tm.initCfg x)
      else coinBranchCfg₀ N₀ N₁ (N₀.tm.initCfg x) := by
  cases b
  · refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp [NDTM.stepWith, coinBranch, coinBranchCfg₀, Cfg.init]
    · simp [NDTM.stepWith, coinBranch, coinBranchCfg₀, Cfg.init]
    · funext j z
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [NDTM.stepWith, coinBranch, coinBranchCfg₀, Cfg.init]
    · funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [NDTM.stepWith, coinBranch, coinBranchCfg₀, Cfg.init]
    · simp [NDTM.stepWith, coinBranch, coinBranchCfg₀, Cfg.init]
  · refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp [NDTM.stepWith, coinBranch, coinBranchCfg₁, Cfg.init]
    · simp [NDTM.stepWith, coinBranch, coinBranchCfg₁, Cfg.init]
    · funext j z
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [NDTM.stepWith, coinBranch, coinBranchCfg₁, Cfg.init]
    · funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [NDTM.stepWith, coinBranch, coinBranchCfg₁, Cfg.init]
    · simp [NDTM.stepWith, coinBranch, coinBranchCfg₁, Cfg.init]

/-- **The dispatcher's run**: under the coins `b :: w`, the dispatcher runs `N_b` under `w`
from its initial configuration (one step later). -/
theorem coinBranch_runWith (b : Bool) (w : List Bool) :
    (coinBranch N₀ N₁).tm.runWith (b :: w) ((coinBranch N₀ N₁).tm.initCfg x) =
      if b then coinBranchCfg₁ N₀ N₁ (N₁.tm.runWith w (N₁.tm.initCfg x))
      else coinBranchCfg₀ N₀ N₁ (N₀.tm.runWith w (N₀.tm.initCfg x)) := by
  rw [NDTM.runWith_cons, coinBranch_stepWith_init]
  cases b
  · exact coinBranch_runWith₀ N₀ N₁ w _
  · exact coinBranch_runWith₁ N₀ N₁ w _

end FinNDTM

end Turing
