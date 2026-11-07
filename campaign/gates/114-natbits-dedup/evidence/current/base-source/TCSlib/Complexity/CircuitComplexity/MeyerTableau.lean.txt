/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Size
import TCSlib.Complexity.CircuitComplexity.MeyerTab

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the head-relative tableau

The semantic layer of the proof of [AB09, Thm 6.20]: the *head-relative tableau* of a
run of `M` and its *local rule*. For a configuration `c` of `M` on input `x`:

* `Complexity.Meyer.RW c h d` — the content of work tape `h` at offset `d ∈ ℤ` from its
  head;
* `Complexity.Meyer.RI c d` — the input symbol at offset `d` from the input head (the
  input `x` padded with blanks, `Complexity.Meyer.xhat`).

One step of `M` changes these only locally: the new state and output summary, and every
cell at offset `d` after the step, are determined by the state, the symbols under the
heads, and the cell at offset `d + m` before the step (`m` the head's move) — or, at the
cell just left, by the written symbol (`RW_step`, `RI_step`). This is what lets the
`Σ₂` verifier check a guessed tableau with a constant number of queries per instance.

## Main definitions

* `Complexity.Meyer.xhat`, `Complexity.Meyer.RW`, `Complexity.Meyer.RI`.
* `Complexity.Meyer.sgnZ` — the signed offset `±a`.
* (width-`w` words are `Complexity.enumWord` of `ClassNP/EXP.lean`, with lemmas here.)

## Main results

* `Complexity.Meyer.tabAns_sym_some`, `Complexity.Meyer.tabAns_sym_none` — the
  tableau machine's walked answers are the head-relative cells.
* `Complexity.Meyer.RW_step`, `Complexity.Meyer.RI_step`, `Complexity.Meyer.SS_step` —
  the local rule of one step.
* `Complexity.Meyer.tabFun_query` — the answer to a well-formed query.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Turing.FinTM Complexity.TimeHierarchy

/-! ### Head-relative cells -/

/-- The input padded with blanks: position `z ≥ 1` holds `x[z - 1]` (blank beyond the
input), positions `z ≤ 0` are blank. -/
def xhat (x : List Bool) (z : ℤ) : Option Bool :=
  if 1 ≤ z then x[(z - 1).toNat]? else none

/-- The signed offset `-a` (for `neg`) or `a`. -/
def sgnZ (neg : Bool) (a : ℕ) : ℤ := if neg then -(a : ℤ) else a

variable {M : FinTM Bool} {x : List Bool}

/-- **Work tape `h` at offset `d` from its head.** -/
def RW (c : Cfg M.k Bool M.State x) (h : Fin M.k) (d : ℤ) : Option Bool :=
  c.workTapes h (c.workTapePos h + d)

/-- **The input at offset `d` from the input head.** -/
def RI (c : Cfg M.k Bool M.State x) (d : ℤ) : Option Bool :=
  xhat x ((c.inputPos.val : ℤ) + d)

/-- The input symbol is the input cell at offset `0`. -/
theorem inputSymbol_eq_xhat (c : Cfg M.k Bool M.State x) :
    c.inputSymbol = RI c 0 := by
  simp only [RI, add_zero, xhat]
  by_cases h0 : c.inputPos.val = 0
  · have : c.inputPos = 0 := Fin.ext h0
    simp [Cfg.inputSymbol, this]
  · have hp := c.inputPos.isLt
    rw [if_pos (by omega)]
    have h := inputSymbol_at c (c.inputPos.val - 1) (by omega) (by omega)
    rw [h]
    congr 1
    omega

/-- The work symbols are the work cells at offset `0`. -/
theorem workTapeSymbols_eq_RW (c : Cfg M.k Bool M.State x) (h : Fin M.k) :
    c.workTapeSymbols h = RW c h 0 := by
  simp [Cfg.workTapeSymbols, RW]

/-! ### The walked answers -/

/-- Walking right on the input clamps at the right boundary. -/
theorem iterate_move_pos {n : ℕ} (p : Fin (n + 2)) (a : ℕ) :
    ((fun q => moveInputPos q .pos)^[a] p).val = min (p.val + a) (n + 1) := by
  induction a generalizing p with
  | zero => simp; omega
  | succ a ih =>
    rw [Function.iterate_succ_apply, ih]
    by_cases hp : p.val = n + 1
    · have : moveInputPos p .pos = p := by
        have he : p = ⟨n + 1, by omega⟩ := Fin.ext hp
        rw [he]; exact moveInputPos_rightBoundary
      rw [this]; omega
    · rw [moveInputPos_pos_of_ne_right _ hp]; simp; omega

/-- Walking left on the input clamps at the left boundary. -/
theorem iterate_move_neg {n : ℕ} (p : Fin (n + 2)) (a : ℕ) :
    ((fun q => moveInputPos q .neg)^[a] p).val = p.val - a := by
  induction a generalizing p with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply, ih]
    by_cases hp : p = 0
    · subst hp
      rw [show moveInputPos (0 : Fin (n + 2)) .neg = 0 from moveInputPos_leftBoundary]
      simp
    · rw [moveInputPos_neg_of_ne_left _ hp]; simp; omega

/-- The input walk of `a` cells. -/
theorem wstep_none_iterate (neg bl : Bool) (c : Cfg M.k Bool M.State x) (a : ℕ) :
    (wstep M (.sym none neg bl))^[a] c =
      { c with inputPos := (fun q => moveInputPos q (walkDir neg))^[a] c.inputPos } := by
  induction a generalizing c with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    rfl

/-- **The walked input answer** is the input cell at the signed offset. -/
theorem walked_input (neg bl : Bool) (c : Cfg M.k Bool M.State x) (a : ℕ) :
    ((wstep M (.sym none neg bl))^[a] c).inputSymbol = RI c (sgnZ neg a) := by
  rw [wstep_none_iterate, inputSymbol_eq_xhat]
  simp only [RI, add_zero, xhat, sgnZ]
  have hp := c.inputPos.isLt
  cases neg
  · simp only [walkDir, Bool.false_eq_true, if_false]
    rw [iterate_move_pos]
    by_cases hle : c.inputPos.val + a ≤ x.length + 1
    · rw [min_eq_left hle]; push_cast; rfl
    · rw [min_eq_right (by omega)]
      rw [if_pos (by omega), if_pos (by omega)]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · simp only [walkDir, if_true]
    rw [iterate_move_neg]
    by_cases hle : a ≤ c.inputPos.val
    · rw [show ((c.inputPos.val - a : ℕ) : ℤ) = (c.inputPos.val : ℤ) + -(a : ℤ) by omega]
    · rw [show c.inputPos.val - a = 0 by omega]
      simp only [Nat.cast_zero]
      rw [if_neg (by omega), if_neg (by omega)]

/-- The work walk of `a` cells. -/
theorem wstep_some_iterate (h : Fin M.k) (neg bl : Bool) (c : Cfg M.k Bool M.State x) (a : ℕ) :
    (wstep M (.sym (some h) neg bl))^[a] c =
      { c with
        workTapePos := (Function.update c.workTapePos h (c.workTapePos h + sgnZ neg a)) } := by
  induction a generalizing c with
  | zero => cases c; simp [sgnZ]
  | succ a ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [wstep, Function.update_self, sgnZ, walkDir]
    congr 1
    funext i
    by_cases hi : i = h
    · subst hi; cases neg <;> simp <;> ring
    · simp [Function.update_of_ne hi]

/-- **The walked work answer** is the work cell at the signed offset. -/
theorem walked_work (h : Fin M.k) (neg bl : Bool) (c : Cfg M.k Bool M.State x) (a : ℕ) :
    ((wstep M (.sym (some h) neg bl))^[a] c).workTapeSymbols h = RW c h (sgnZ neg a) := by
  rw [wstep_some_iterate]
  simp [Cfg.workTapeSymbols, RW]

/-- **The tableau answer for a work-cell selector.** -/
theorem tabAns_sym_some (h : Fin M.k) (neg bl : Bool) (c : Cfg M.k Bool M.State x) (a : ℕ) :
    tabAns M (.sym (some h) neg bl) c a = symBit bl (RW c h (sgnZ neg a)) := by
  simp only [tabAns, selAnswer, walked_work]

/-- **The tableau answer for an input-cell selector.** -/
theorem tabAns_sym_none (neg bl : Bool) (c : Cfg M.k Bool M.State x) (a : ℕ) :
    tabAns M (.sym none neg bl) c a = symBit bl (RI c (sgnZ neg a)) := by
  simp only [tabAns, selAnswer, walked_input]

/-- **The tableau answer for a state selector.** -/
theorem tabAns_st (σ : Option M.State) (r₀ : OutReg) (c : Cfg M.k Bool M.State x) (a : ℕ) :
    tabAns M (.st σ r₀) c a = decide (c.state = σ ∧ OutReg.ofList c.output = r₀) := by
  simp only [tabAns, selAnswer]

/-! ### The local rule -/

variable (M) in
/-- The symbols under the heads: the input symbol and the work symbols. -/
abbrev Rd := Option Bool × (Fin M.k → Option Bool)

/-- The reads of a configuration. -/
def reads (c : Cfg M.k Bool M.State x) : Rd M := (RI c 0, fun h => RW c h 0)

/-- The state and output summary of a configuration. -/
def SS (c : Cfg M.k Bool M.State x) : Option M.State × OutReg := (c.state, OutReg.ofList c.output)

variable (M) in
/-- **The local rule for the state**: a live state takes its transition, emitting into
the summary; a halted one stays. -/
def ruleS (σ : Option M.State × OutReg) (ρ : Rd M) : Option M.State × OutReg :=
  match σ.1 with
  | none => σ
  | some q => ((M.tm.tr q ρ.1 ρ.2).state, σ.2.push (M.tm.tr q ρ.1 ρ.2).output)

/-- The symbol at the head after an optional write `w` over the read symbol `r`. -/
def wsym (w : Option (Option Bool)) (r : Option Bool) : Option Bool :=
  match w with
  | none => r
  | some s => s

variable (M) in
/-- **The local rule for a work cell**: with move `m` and write `w` on tape `h`, the cell
at offset `d` afterwards is the written symbol if `d + m = 0`, else the old cell at
offset `d + m`; nothing changes if halted. `f` is the old row of tape `h`. -/
def ruleW (oq : Option M.State) (ρ : Rd M) (h : Fin M.k) (d : ℤ) (f : ℤ → Option Bool) :
    Option Bool :=
  match oq with
  | none => f d
  | some q =>
    if d + ((M.tm.tr q ρ.1 ρ.2).workTapes h).2 = 0 then
      wsym ((M.tm.tr q ρ.1 ρ.2).workTapes h).1 (ρ.2 h)
    else f (d + ((M.tm.tr q ρ.1 ρ.2).workTapes h).2)

variable (M) in
/-- **The local rule for an input cell**: the input head moves by `m` unless the move is
clamped — detected as "blank under the head and blank at offset `m`" — and nothing
changes if halted. `f` is the old input row. -/
def ruleI (oq : Option M.State) (ρ : Rd M) (d : ℤ) (f : ℤ → Option Bool) : Option Bool :=
  match oq with
  | none => f d
  | some q =>
    if ρ.1 = none ∧ f ((M.tm.tr q ρ.1 ρ.2).inputTape) = none then f d
    else f (d + (M.tm.tr q ρ.1 ρ.2).inputTape)

/-- One step of a live configuration in terms of its reads. -/
theorem step_eq (c : Cfg M.k Bool M.State x) (q : M.State) (hq : c.state = some q) :
    M.tm.step c = (M.tm.tr q (reads c).1 (reads c).2).apply c := by
  have h1 : c.workTapeSymbols = (reads c).2 := by
    funext h; simp [reads, workTapeSymbols_eq_RW]
  simp only [MultiTapeTM.step, hq, inputSymbol_eq_xhat]
  rw [h1]
  rfl

/-- **The local rule for the state** holds along a run. -/
theorem SS_step (c : Cfg M.k Bool M.State x) : SS (M.tm.step c) = ruleS M (SS c) (reads c) := by
  cases hq : c.state with
  | none => simp [SS, ruleS, hq]
  | some q =>
    rw [step_eq c q hq]
    simp [SS, ruleS, hq, Action.apply, OutReg.ofList_push]

/-- **The local rule for work cells** holds along a run. -/
theorem RW_step (c : Cfg M.k Bool M.State x) (h : Fin M.k) (d : ℤ) :
    RW (M.tm.step c) h d = ruleW M c.state (reads c) h d (RW c h) := by
  cases hq : c.state with
  | none => simp [ruleW, MultiTapeTM.step_of_halt hq]
  | some q =>
    rw [step_eq c q hq]
    simp only [RW, ruleW, Action.apply]
    generalize ((M.tm.tr q (reads c).1 (reads c).2).workTapes h) = wm
    obtain ⟨w, m⟩ := wm
    cases w with
    | none =>
      simp only [wsym]
      split_ifs with hd
      · simp [reads, RW]; congr 1; omega
      · congr 1; ring
    | some s =>
      simp only [wsym]
      split_ifs with hd
      · rw [Function.update_apply, if_pos (by omega)]
      · rw [Function.update_apply, if_neg (by omega)]; congr 1; ring

/-- Blank input cells are exactly the cells outside `[1, |x|]`. -/
theorem xhat_eq_none (z : ℤ) : xhat x z = none ↔ z < 1 ∨ (x.length : ℤ) < z := by
  simp only [xhat]
  split_ifs with h
  · rw [List.getElem?_eq_none_iff]; omega
  · simp; omega

/-- **The local rule for input cells** holds along a run.

**Proof sketch.** Case on the move: an unclamped move shifts the offset by `m`; a clamped
move happens exactly at a boundary, where the cell under the head and at offset `m` are
blank — and if the head is inside with both blank, the input is empty and every cell is
blank. -/
theorem RI_step (c : Cfg M.k Bool M.State x) (d : ℤ) :
    RI (M.tm.step c) d = ruleI M c.state (reads c) d (RI c) := by
  cases hq : c.state with
  | none => simp [ruleI, MultiTapeTM.step_of_halt hq]
  | some q =>
    rw [step_eq c q hq]
    simp only [RI, ruleI, Action.apply]
    generalize (M.tm.tr q (reads c).1 (reads c).2).inputTape = m
    have hp := c.inputPos.isLt
    have hr : (reads c).1 = xhat x (c.inputPos.val : ℤ) := by simp [reads, RI]
    rw [hr]
    cases m with
    | zero => simp
    | pos =>
      by_cases he : c.inputPos.val = x.length + 1
      · have hpe : c.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext he
        rw [hpe, show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) SignType.pos =
          ⟨x.length + 1, by omega⟩ from moveInputPos_rightBoundary]
        rw [if_pos ⟨(xhat_eq_none _).mpr (by right; omega),
          (xhat_eq_none _).mpr (by right; simp; omega)⟩]
      · rw [moveInputPos_pos_of_ne_right _ he]
        split_ifs with hc
        · -- clamping condition with the head inside: the input is empty
          have h1 := (xhat_eq_none _).mp hc.1
          have h2 := (xhat_eq_none _).mp hc.2
          have hx : x.length = 0 := by simp at h2; omega
          rw [(xhat_eq_none _).mpr (by omega), (xhat_eq_none _).mpr (by omega)]
        · congr 1; simp; ring
    | neg =>
      by_cases he : c.inputPos = 0
      · rw [he, show moveInputPos (0 : Fin (x.length + 2)) .neg = 0 from
          moveInputPos_leftBoundary]
        rw [if_pos ⟨(xhat_eq_none _).mpr (by left; simp), (xhat_eq_none _).mpr (by left; simp)⟩]
      · have h0 : c.inputPos.val ≠ 0 := fun h => he (Fin.ext h)
        rw [moveInputPos_neg_of_ne_left _ he]
        split_ifs with hc
        · have h1 := (xhat_eq_none _).mp hc.1
          have h2 := (xhat_eq_none _).mp hc.2
          have hx : x.length = 0 := by simp at h2; omega
          rw [(xhat_eq_none _).mpr (by omega), (xhat_eq_none _).mpr (by omega)]
        · congr 1; simp; omega

/-! ### The initial row -/

/-- The initial state and output summary. -/
theorem SS_init : SS (M.tm.initCfg x) = (some M.tm.q₀, OutReg.empty) := rfl

/-- The initial work tapes are blank. -/
theorem RW_init (h : Fin M.k) (d : ℤ) : RW (M.tm.initCfg x) h d = none := rfl

/-- The initial input row: the head is on the first input cell. -/
theorem RI_init (d : ℤ) : RI (M.tm.initCfg x) d = xhat x (1 + d) := rfl

/-! ### Width-`w` binary words

The words are `Complexity.enumWord` (`ClassNP/EXP.lean`), the enumerator's width-`w`
little-endian code. -/

/-- The word has width `w`. -/
@[simp] theorem length_enumWord (w v : ℕ) : (enumWord w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [enumWord, ih]

/-- The value of a width-`w` word of a number below `2^w`. -/
theorem ctrVal_enumWord (w v : ℕ) (hv : v < 2 ^ w) : ctrVal (enumWord w v) = v := by
  induction w generalizing v with
  | zero => simp at hv; subst hv; rfl
  | succ w ih =>
    simp only [enumWord, ctrVal]
    rw [ih (v / 2) (by rw [pow_succ] at hv; omega)]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h] <;> omega

/-- Every width-`w` word is the word of its value. -/
theorem enumWord_ctrVal (u : List Bool) : enumWord u.length (ctrVal u) = u := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [List.length_cons, enumWord, ctrVal]
    cases b
    · simp only [Bool.false_eq_true, if_false, zero_add]
      rw [show 2 * ctrVal u / 2 = ctrVal u by omega, ih]
      simp
    · simp only [if_true]
      rw [show (1 + 2 * ctrVal u) / 2 = ctrVal u by omega, ih]
      simp only [List.cons.injEq, and_true]
      simp

/-- The width-`w` word of `0` is all `false`. -/
theorem enumWord_zero (w : ℕ) : enumWord w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [enumWord, ih, List.replicate_succ]

/-- The width-`w` word of `2^w - 1` is all `true`. -/
theorem enumWord_ones (w : ℕ) : enumWord w (2 ^ w - 1) = List.replicate w true := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [enumWord, List.replicate_succ]
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    rw [show (2 ^ (w + 1) - 1) / 2 = 2 ^ w - 1 by rw [pow_succ]; omega, ih]
    simp only [List.cons.injEq, and_true, decide_eq_true_eq]
    rw [pow_succ]; omega

/-- **Fixed-width increment** on words of numbers: `v + 1 < 2^w` increments. -/
theorem incFixed_enumWord (w v : ℕ) (hv : v + 1 < 2 ^ w) :
    incFixed (enumWord w v) = some (enumWord w (v + 1)) := by
  induction w generalizing v with
  | zero => simp at hv
  | succ w ih =>
    simp only [enumWord]
    rcases Nat.even_or_odd v with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      simp only [show (k + k) % 2 = 0 by omega, show (k + k + 1) % 2 = 1 by omega,
        show (k + k) / 2 = k by omega, show (k + k + 1) / 2 = k by omega]
      simp [incFixed]
    · subst hk
      simp only [show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1 + 1) % 2 = 0 by omega,
        show (2 * k + 1) / 2 = k by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
      simp [incFixed, ih k (by rw [pow_succ] at hv; omega)]

/-- Increment overflows exactly on the all-`true` word. -/
theorem incFixed_eq_none_iff (u : List Bool) : incFixed u = none ↔ u = List.replicate u.length true := by
  induction u with
  | nil => simp [incFixed]
  | cons b u ih =>
    cases b <;> simp [incFixed, ih, List.replicate_succ]

/-- Appending zeros at the high end keeps the value. -/
theorem ctrVal_append_zeros (l : List Bool) (k : ℕ) :
    ctrVal (l ++ List.replicate k false) = ctrVal l := by
  induction l with
  | nil =>
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ctrVal] at ih ⊢; exact ih
  | cons b l ih => simp [ctrVal, ih]

/-- **The padded binary length code**: `Nat.bits j` padded with zeros to width `w` is the
width-`w` word of `j`. -/
theorem bits_pad (w j : ℕ) (hj : j < 2 ^ w) :
    Nat.bits j ++ List.replicate (w - (Nat.bits j).length) false = enumWord w j := by
  have hlen : (Nat.bits j).length ≤ w := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr hj
  have h := enumWord_ctrVal (Nat.bits j ++ List.replicate (w - (Nat.bits j).length) false)
  rw [ctrVal_append_zeros, ctrVal_bits] at h
  simp only [List.length_append, List.length_replicate] at h
  rw [show (Nat.bits j).length + (w - (Nat.bits j).length) = w by omega] at h
  exact h.symm

/-! ### The answer to a well-formed query -/

variable (M) in
/-- **The answer to a well-formed query** is the tableau answer for its decoded fields. -/
theorem tabFun_query (sel : Sel M) (t a x : List Bool) :
    tabFun M (query (encodeSel sel) t a x) =
      tabAns M sel (M.tm.runFrom (M.tm.initCfg x) (ctrVal t)) (ctrVal a) := by
  simp [tabFun, parseQ_query]

end Complexity.Meyer
