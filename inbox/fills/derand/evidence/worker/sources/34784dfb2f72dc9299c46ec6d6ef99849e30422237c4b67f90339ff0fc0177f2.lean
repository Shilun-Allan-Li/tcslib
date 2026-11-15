/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clocked runner: machine and setup phases

[AB09, Theorem 3.1, proof]: the diagonalizing machine of the time hierarchy theorem
runs the universal machine "for `g(|x|)` steps" and then answers. This file builds the
**clocked runner** `clockTM K W` realizing that sentence for an arbitrary (possibly
partial) machine `W`, with the step budget supplied by a second machine `K` (in the
hierarchy theorem, the time-constructibility witness of `g`).

The runner has three tape blocks (`Turing.FinTM.tapeBlocks`): `K`'s work tapes, one
**counter tape**, and `W`'s work tapes. It proceeds in phases:

1. *Budget.* Simulate `K` on the input, redirecting every emission onto the counter
   tape (exactly as phase one of `Turing.FinTM.bufferedCompTM`). The counter then holds
   `K`'s output word `s`, read as a little-endian binary number `ctrVal s`.
2. *Rewind.* Return the counter head to cell `0`, then the input head to the first
   input cell (`Turing.FinTM.timed_rewind`).
3. *Loop* (`ClockState.dec` / `ClockState.ret`). Decrement the counter by a
   little-endian borrow sweep; the step that clears the low `true` bit is fused with
   **one transition of `W`** on its own tape block and the native input, after which
   the counter head returns to cell `0`. `W`'s emissions are not passed to the output;
   they are summarized in a three-valued register `OutReg` ("empty", "one symbol `b`",
   "two or more symbols"). If the borrow sweep runs off the counter (value zero), the
   runner emits `true` and halts (timeout); if `W` halts, the runner emits `false`
   exactly when `W`'s completed output is `[true]`, and halts.

This file contains the machine, its configurations, and the exact run lemmas of the
budget and rewind phases. The loop and the specification `clockTM_spec` are in
`TCSlib.Complexity.TimeHierarchy.ClockLoop`.

## Design

* The runner clocks **its own simulation steps of `W`**, not steps of a machine that
  `W` might itself simulate. This is what makes the hierarchy proof go through in this
  development: the universal machine's per-code constant `C_α` has no uniform bound
  over codes `α` (it contains the representation scheme's abstract canonizer time), so
  a clock on *simulated* steps would not bound the diagonal machine's running time.
* The counter is a binary down-counter, not a unary one, so that a budget `g(n)` costs
  only `O(log g(n))` cells; the amortized analysis (in `ClockLoop.lean`) shows that
  `v` decrements cost `O(v + |s|)` steps in total.

## Main definitions

* `Complexity.TimeHierarchy.OutReg` — the output-summary register.
* `Complexity.TimeHierarchy.ctrVal`, `ctrPop` — value and popcount of a counter word.
* `Complexity.TimeHierarchy.clockTM` — the clocked runner.

## Main results

* `Complexity.TimeHierarchy.clockTM_setup` — from the initial configuration, the
  runner reaches the loop entry with counter word `s = K(x)` and a fresh copy of `W`'s
  initial configuration within `t_K + |s| + |x| + 5` steps.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1 and its proof, p. 69.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-! ### The output-summary register -/

/-- A three-valued summary of a binary word: empty, a single symbol `b`, or two or
more symbols. It is exactly enough to decide whether a completed output is `[true]`. -/
inductive OutReg where
  | empty : OutReg
  | one : Bool → OutReg
  | many : OutReg
  deriving DecidableEq, Fintype

/-- The summary of a word. -/
def OutReg.ofList : List Bool → OutReg
  | [] => .empty
  | [b] => .one b
  | _ :: _ :: _ => .many

/-- The summary after appending an optional emitted symbol. -/
def OutReg.push : OutReg → Option Bool → OutReg
  | r, none => r
  | .empty, some b => .one b
  | .one _, some _ => .many
  | .many, some _ => .many

/-- Appending an optional emission commutes with summarizing. -/
lemma OutReg.ofList_push (w : List Bool) (o : Option Bool) :
    OutReg.ofList (w ++ o.toList) = (OutReg.ofList w).push o := by
  rcases o with _ | b
  · cases h : OutReg.ofList w <;> simp [OutReg.push, h]
  · match w with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rfl

/-- The summary is `one true` exactly for the word `[true]`. -/
lemma OutReg.ofList_eq_one_true (w : List Bool) :
    OutReg.ofList w = .one true ↔ w = [true] := by
  match w with
  | [] => simp [OutReg.ofList]
  | [b] => simp [OutReg.ofList]
  | _ :: _ :: _ => simp [OutReg.ofList]

/-! ### Counter words -/

/-- The little-endian value of a counter word (low bit first; leading zeros at the
high end allowed). -/
def ctrVal : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * ctrVal bs

/-- The number of `true` bits of a counter word. -/
def ctrPop : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + ctrPop bs

/-- The popcount is at most the width. -/
lemma ctrPop_le_length (s : List Bool) : ctrPop s ≤ s.length := by
  induction s with
  | nil => simp [ctrPop]
  | cons b s ih => cases b <;> simp [ctrPop] <;> omega

/-- The value of `Nat.bits n` is `n`. -/
lemma ctrVal_bits (n : ℕ) : ctrVal n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [ctrVal]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [ctrVal, ih, Nat.bit_val]; omega

/-- Low zeros multiply the value by a power of two. -/
lemma ctrVal_replicate_false (j : ℕ) (rest : List Bool) :
    ctrVal (List.replicate j false ++ rest) = 2 ^ j * ctrVal rest := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, ctrVal, ih]
    simp [Nat.pow_succ]
    ring

/-- Low ones contribute `2^j - 1`. -/
lemma ctrVal_replicate_true (j : ℕ) (rest : List Bool) :
    ctrVal (List.replicate j true ++ rest) + 1 = 2 ^ j * (ctrVal rest + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, ctrVal, if_true]
    rw [Nat.pow_succ]
    have : 1 + 2 * ctrVal (List.replicate j true ++ rest) + 1 =
        2 * (ctrVal (List.replicate j true ++ rest) + 1) := by ring
    rw [this, ih]
    ring

/-- One borrow: the value of `0^j 1 rest` exceeds that of `1^j 0 rest` by one. -/
lemma ctrVal_borrow (j : ℕ) (rest : List Bool) :
    ctrVal (List.replicate j true ++ false :: rest) + 1 =
      ctrVal (List.replicate j false ++ true :: rest) := by
  rw [ctrVal_replicate_true, ctrVal_replicate_false]
  simp only [ctrVal, Bool.false_eq_true, if_false, if_true]
  ring

/-- Popcount of a word with a run of low bits. -/
lemma ctrPop_replicate (j : ℕ) (b : Bool) (rest : List Bool) :
    ctrPop (List.replicate j b ++ rest) = (if b then j else 0) + ctrPop rest := by
  induction j with
  | zero => cases b <;> simp
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, ctrPop, ih]
    cases b <;> simp; omega

/-- A word of positive value has a lowest `true` bit. -/
lemma ctrVal_pos_decomp (s : List Bool) (h : ctrVal s ≠ 0) :
    ∃ j rest, s = List.replicate j false ++ true :: rest := by
  induction s with
  | nil => simp [ctrVal] at h
  | cons b s ih =>
    cases b with
    | true => exact ⟨0, s, by simp⟩
    | false =>
      have hs : ctrVal s ≠ 0 := by
        intro h0
        apply h
        simp [ctrVal, h0]
      obtain ⟨j, rest, rfl⟩ := ih hs
      exact ⟨j + 1, rest, by simp [List.replicate_succ]⟩

/-- A word of value zero is all `false`. -/
lemma ctrVal_zero_eq (s : List Bool) (h : ctrVal s = 0) :
    s = List.replicate s.length false := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    cases b with
    | true => simp [ctrVal] at h
    | false =>
      have hs : ctrVal s = 0 := by simp [ctrVal] at h; omega
      simp [List.replicate_succ, ← ih hs]

/-! ### The machine -/

/-- Control states of the clocked runner: simulating the budget machine (`none` =
the budget machine has just halted), rewinding the counter, rewinding the input,
and the two loop phases carrying the simulated machine's live state and output
register. -/
inductive ClockState (KS WS : Type) where
  | kRun : Option KS → ClockState KS WS
  | cScan : ClockState KS WS
  | iStart : ClockState KS WS
  | iScan : ClockState KS WS
  | dec : WS → OutReg → ClockState KS WS
  | ret : WS → OutReg → ClockState KS WS
  deriving DecidableEq, Fintype

/-- The index of the counter tape in the three-block layout. -/
def ctrIdx (kK kW : ℕ) : Fin (kK + (1 + kW)) := Fin.natAdd kK (Fin.castAdd kW (0 : Fin 1))

/-- An action touching only the counter tape: write `w`, move `d`, go to `q`. -/
def ctrAction {kK kW : ℕ} {S : Type} (w : Option (Option Bool)) (d : SignType)
    (q : Option S) : Action (kK + (1 + kW)) Bool S :=
  ⟨0, tapeBlocks (fun _ => (none, 0)) (w, d) (fun _ => (none, 0)), none, q⟩

/-- The transition table of the clocked runner (see the module docstring). -/
def clockTr (K W : FinTM Bool) (q : ClockState K.State W.State) (inp : Option Bool)
    (work : Fin (K.k + (1 + W.k)) → Option Bool) :
    Action (K.k + (1 + W.k)) Bool (ClockState K.State W.State) :=
  match q with
  | .kRun (some q) =>
    let a := K.tm.tr q inp (fun i => work (Fin.castAdd (1 + W.k) i))
    ⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.kRun a.state)⟩
  | .kRun none => ctrAction none .neg (some .cScan)
  | .cScan =>
    if work (ctrIdx K.k W.k) = none then ctrAction none .pos (some .iStart)
    else ctrAction none .neg (some .cScan)
  | .iStart => controlAction .neg (some .iScan)
  | .iScan =>
    match inp with
    | some _ => controlAction .neg (some .iScan)
    | none => controlAction .pos (some (.dec W.tm.q₀ .empty))
  | .dec q r =>
    match work (ctrIdx K.k W.k) with
    | none => ⟨0, fun _ => (none, 0), some true, none⟩
    | some false => ctrAction (some (some true)) .pos (some (.dec q r))
    | some true =>
      let a := W.tm.tr q inp (fun i => work (Fin.natAdd K.k (Fin.natAdd 1 i)))
      ⟨a.inputTape, tapeBlocks (fun _ => (none, 0)) (some (some false), .neg) a.workTapes,
        (if a.state = none then some (decide (r.push a.output ≠ .one true)) else none),
        a.state.map (fun q' => .ret q' (r.push a.output))⟩
  | .ret q r =>
    if work (ctrIdx K.k W.k) = none then ctrAction none .pos (some (.dec q r))
    else ctrAction none .neg (some (.ret q r))

/-- **The clocked runner** `clockTM K W` [AB09, Theorem 3.1, proof of the hierarchy
theorem, "run `M_x` for `g(|x|)` steps"]: compute the budget word `K(x)` onto a
counter tape, then alternate one step of `W` (on the native input, with emissions
summarized in a register) with one binary decrement of the counter; answer `true` on
counter underflow, and on `W`'s halting answer whether `W`'s output differs from
`[true]`. See the module docstring for the phases. -/
def clockTM (K W : FinTM Bool) : FinTM Bool where
  k := K.k + (1 + W.k)
  State := ClockState K.State W.State
  tm := { q₀ := .kRun (some K.tm.q₀), tr := clockTr K W }

/-! ### Configurations -/

variable (K W : FinTM Bool)

/-- One step from a live configuration applies the transition table. -/
lemma clockTM_step_some {x : List Bool}
    (c : Cfg (clockTM K W).k Bool (clockTM K W).State x) (q : ClockState K.State W.State)
    (h : c.state = some q) :
    (clockTM K W).tm.step c = (clockTr K W q c.inputSymbol c.workTapeSymbols).apply c := by
  unfold MultiTapeTM.step
  rw [h]
  rfl

/-- Budget phase: `K`'s configuration in the left block, its emitted word on the
counter tape with the counter head on the right blank, the right block blank. -/
def kCfg {x : List Bool} (c : Cfg K.k Bool K.State x) :
    Cfg (clockTM K W).k Bool (clockTM K W).State x where
  state := some (.kRun c.state)
  inputPos := c.inputPos
  workTapes := tapeBlocks c.workTapes (bufferTape c.output) (fun _ _ => none)
  workTapePos := tapeBlocks c.workTapePos c.output.length (fun _ => 0)
  output := []

/-- The initial configuration is the embedded initial budget configuration. -/
lemma kCfg_init (x : List Bool) :
    (clockTM K W).tm.initCfg x = kCfg K W (K.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [kCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [kCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [kCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [kCfg, tapeBlocks]

/-- One live budget step: the left block and input head follow `K`; an emission is
appended to the counter word.

**Proof sketch.** As `Turing.FinTM.bufferedFirstCfg_step`: reads of the left block are
`K`'s reads, a non-emitting step leaves the counter fixed, and an emitting step writes
the right blank (`Turing.FinTM.bufferTape_append`) and advances the counter head. -/
lemma kCfg_step {x : List Bool} (c : Cfg K.k Bool K.State x) (hs : c.state ≠ none) :
    (clockTM K W).tm.step (kCfg K W c) = kCfg K W (K.tm.step c) := by
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    rw [clockTM_step_some K W _ (.kRun (some q)) (by simp [kCfg, hq])]
    have hr : (fun i => (kCfg K W c).workTapeSymbols (Fin.castAdd (1 + W.k) i)) =
        c.workTapeSymbols := by
      funext i
      simp [kCfg, Cfg.workTapeSymbols]
    have hi : (kCfg K W c).inputSymbol = c.inputSymbol := rfl
    simp only [clockTr]
    rw [hr, hi]
    have hstep : K.tm.step c = (K.tm.tr q c.inputSymbol c.workTapeSymbols).apply c := by
      unfold MultiTapeTM.step; rw [hq]
    rw [hstep]
    generalize K.tm.tr q c.inputSymbol c.workTapeSymbols = a
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [kCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [kCfg, Action.apply, ho, bufferTape_append]
        · intro j; simp [kCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [kCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [kCfg, Action.apply, ho]
        · intro j; simp [kCfg, Action.apply]
    · simp [kCfg, Action.apply]

/-- Budget-phase lockstep up to and including `K`'s first halting transition. -/
lemma kCfg_run {x : List Bool} (c : Cfg K.k Bool K.State x) (t : ℕ)
    (h : ∀ s, s < t → (K.tm.runFrom c s).state ≠ none) :
    (clockTM K W).tm.runFrom (kCfg K W c) t = kCfg K W (K.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      kCfg_step K W _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Loop-phase configurations: the state `st`, the simulated machine's configuration
`c` in the right block (its input head is the native one), an arbitrary counter tape
`τ` with head `z`, a frozen left block, and real output `out`. -/
def ctrCfg {x : List Bool} (st : Option (ClockState K.State W.State))
    (c : Cfg W.k Bool W.State x) (τ : ℤ → Option Bool) (z : ℤ)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (out : List Bool) :
    Cfg (clockTM K W).k Bool (clockTM K W).State x where
  state := st
  inputPos := c.inputPos
  workTapes := tapeBlocks kt τ c.workTapes
  workTapePos := tapeBlocks kh z c.workTapePos
  output := out

/-- The counter read of a loop configuration. -/
lemma ctrCfg_ctr {x : List Bool} (st : Option (ClockState K.State W.State))
    (c : Cfg W.k Bool W.State x) (τ : ℤ → Option Bool) (z : ℤ)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (out : List Bool) :
    (ctrCfg K W st c τ z kt kh out).workTapeSymbols (ctrIdx K.k W.k) = τ z := by
  simp [ctrCfg, Cfg.workTapeSymbols, ctrIdx]

/-- The right-block reads of a loop configuration are the simulated machine's reads. -/
lemma ctrCfg_right {x : List Bool} (st : Option (ClockState K.State W.State))
    (c : Cfg W.k Bool W.State x) (τ : ℤ → Option Bool) (z : ℤ)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (out : List Bool) :
    (fun i => (ctrCfg K W st c τ z kt kh out).workTapeSymbols
      (Fin.natAdd K.k (Fin.natAdd 1 i))) = c.workTapeSymbols := by
  funext i
  simp [ctrCfg, Cfg.workTapeSymbols]

/-- Applying a counter-only action (optional write `w` to the counter cell, counter head
move `d`, next state `q`) to a loop configuration yields the loop configuration with
state `q`, counter tape updated at the head by `w`, counter head at `z + d`, and all
other blocks unchanged.

**Proof sketch.** Compare the two configurations componentwise: the state and output
agree by definition of the action, and the input head does not move. For the tape
contents and head positions, split the work tapes into the `K` block, the counter
tape, and the `W` block; on the `K` and `W` blocks the action writes nothing and stays
put, and on the counter tape case analysis on `w` gives the update and the move. -/
lemma ctrAction_apply {x : List Bool} (st : Option (ClockState K.State W.State))
    (c : Cfg W.k Bool W.State x) (τ : ℤ → Option Bool) (z : ℤ)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (out : List Bool)
    (w : Option (Option Bool)) (d : SignType) (q : Option (ClockState K.State W.State)) :
    (ctrAction (kK := K.k) (kW := W.k) w d q).apply (ctrCfg K W st c τ z kt kh out) =
      ctrCfg K W q c (match w with | none => τ | some v => Function.update τ z v)
        (z + d) kt kh out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [ctrAction, ctrCfg])
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [ctrAction, ctrCfg, Action.apply]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j
        cases w <;> simp [ctrAction, ctrCfg, Action.apply]
      · intro j; simp [ctrAction, ctrCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [ctrAction, ctrCfg, Action.apply]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [ctrAction, ctrCfg, Action.apply]

/-! ### Rewinding the counter and the input -/

/-- Counter scan configuration: the counter head at cell `j - 1`, the right block
blank, the left block frozen. -/
def cScanCfg {x : List Bool} (s : List Bool) (p : Fin (x.length + 2))
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (j : ℕ) :
    Cfg (clockTM K W).k Bool (clockTM K W).State x :=
  ctrCfg K W (some .cScan) ⟨none, p, fun _ _ => none, fun _ => 0, []⟩ (bufferTape s)
    ((j : ℤ) - 1) kt kh []

/-- Scanning left from cell `j - 1` of a stored word reaches cell `0` and the input
rewind state in exactly `j + 1` steps.

**Proof sketch.** As `Turing.FinTM.bufferedScanCfg_run`: at `j = 0` the head reads the
left blank and moves right; at `j + 1` it reads a stored symbol and moves left. -/
lemma cScanCfg_run {x : List Bool} (s : List Bool) (p : Fin (x.length + 2))
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) : ∀ j, j ≤ s.length →
    (clockTM K W).tm.runFrom (cScanCfg K W s p kt kh j) (j + 1) =
      ctrCfg K W (some .iStart) ⟨none, p, fun _ _ => none, fun _ => 0, []⟩ (bufferTape s)
        0 kt kh [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      clockTM_step_some K W _ .cScan rfl]
    simp only [clockTr, cScanCfg, ctrCfg_ctr, Nat.cast_zero, zero_sub, bufferTape_left,
      if_true]
    rw [ctrAction_apply]
    simp
  | succ j ih =>
    intro hj
    have hread : bufferTape s (((j + 1 : ℕ) : ℤ) - 1) = some s[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hstep : (clockTM K W).tm.step (cScanCfg K W s p kt kh (j + 1)) =
        cScanCfg K W s p kt kh j := by
      rw [clockTM_step_some K W _ .cScan rfl]
      simp only [clockTr, cScanCfg, ctrCfg_ctr, hread, reduceCtorEq, if_false]
      rw [ctrAction_apply]
      congr 1
      push_cast
      simp [SignType.neg_eq_neg_one]
      ring
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (by omega)

/-- From a halted budget configuration, the counter rewind takes exactly
`|s| + 2` steps, where `s` is the budget word. -/
lemma kCfg_rewind {x : List Bool} (c : Cfg K.k Bool K.State x) (hs : c.state = none) :
    (clockTM K W).tm.runFrom (kCfg K W c) (c.output.length + 2) =
      ctrCfg K W (some .iStart) ⟨none, c.inputPos, fun _ _ => none, fun _ => 0, []⟩
        (bufferTape c.output) 0 c.workTapes c.workTapePos [] := by
  have hstep : (clockTM K W).tm.step (kCfg K W c) =
      cScanCfg K W c.output c.inputPos c.workTapes c.workTapePos c.output.length := by
    rw [clockTM_step_some K W _ (.kRun none) (by simp [kCfg, hs])]
    simp only [clockTr]
    have he : kCfg K W c = ctrCfg K W (some (.kRun none))
        ⟨none, c.inputPos, fun _ _ => none, fun _ => 0, []⟩ (bufferTape c.output)
        c.output.length c.workTapes c.workTapePos [] := by
      refine Cfg.ext (by simp [kCfg, ctrCfg, hs]) rfl rfl rfl rfl
    rw [he, ctrAction_apply]
    simp only [cScanCfg]
    congr 1
  rw [show c.output.length + 2 = (c.output.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact cScanCfg_run K W c.output c.inputPos c.workTapes c.workTapePos _ (le_refl _)

/-- **Setup.** If `K` halts on `x` with output `s` within `tK` steps, the runner
reaches the loop entry — state `dec q₀ empty`, counter word `s` with its head on cell
`0`, and `W`'s initial configuration in the right block — within
`tK + |s| + |x| + 5` steps.

**Proof sketch.** Run the budget phase to `K`'s first halting time (lockstep,
`kCfg_run`), identify the counter word with `s` by determinism, rewind the counter in
`|s| + 2` steps (`kCfg_rewind`), and rewind the input in at most `|x| + 3` steps
(`Turing.FinTM.timed_rewind`, whose end configuration is the loop entry since the
right block was never touched). -/
lemma clockTM_setup (x s : List Bool) (tK : ℕ) (hK : K.ComputesInTime x s tK) :
    ∃ (a : ℕ) (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ),
      a ≤ tK + s.length + x.length + 5 ∧
      (clockTM K W).tm.runFrom ((clockTM K W).tm.initCfg x) a =
        ctrCfg K W (some (.dec W.tm.q₀ .empty)) (W.tm.initCfg x) (bufferTape s) 0 kt kh [] := by
  classical
  have hh : ∃ t, (K.tm.runFrom (K.tm.initCfg x) t).state = none :=
    ⟨tK, ((computesInTime_iff K x s tK).mp hK).1⟩
  let t := Nat.find hh
  let c := K.tm.runFrom (K.tm.initCfg x) t
  have hs : c.state = none := Nat.find_spec hh
  have ht : t ≤ tK := Nat.find_min' hh ((computesInTime_iff K x s tK).mp hK).1
  have hc : K.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = s := hc.output_unique hK
  -- the input rewind
  let start := ctrCfg K W (some .iStart) ⟨none, c.inputPos, fun _ _ => none, fun _ => 0, []⟩
    (bufferTape c.output) 0 c.workTapes c.workTapePos []
  obtain ⟨r, hr, hrun⟩ := timed_rewind (clockTM K W).tm ClockState.iStart ClockState.iScan
    (some (.dec W.tm.q₀ .empty)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    start rfl
  refine ⟨t + (c.output.length + 2) + r, c.workTapes, c.workTapePos, ?_, ?_⟩
  · have hp : start.inputPos.val ≤ x.length + 1 := by
      have := start.inputPos.isLt
      omega
    rw [ho] at *
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, kCfg_init,
      kCfg_run K W _ t (fun s hs => Nat.find_min hh hs), kCfg_rewind K W c hs, hrun, ← ho]
    rfl

end Complexity.TimeHierarchy
