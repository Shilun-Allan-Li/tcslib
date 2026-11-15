/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Virtual-input layout for subroutine calls

When a logspace machine calls a decider on an input it cannot afford to write down, it
presents a *virtual input* assembled from pieces it does have: a part of its own input and
short words held on work tapes [AB09, proof of Lemma 4.17, Fig. 4.3]. This file fixes the
shape of such virtual inputs and the bookkeeping of a head walking over them, as pure list
and arithmetic facts; the machines that realize the walk are in
`TCSlib.Complexity.SpaceComplexity.Machines.Sim` (a call's decider run on the virtual
input) with `TCSlib.Complexity.SpaceComplexity.Machines.CallReturn` and
`TCSlib.Complexity.SpaceComplexity.Machines.Call` (entry and return).

A virtual input is a list of *segments* `(w, d)`, a word `w` rendered doubled (`d = true`,
each bit written twice) or plain, joined by the separator `[false, true]`. With two
segments `[(x, true), (y, false)]` this is exactly `Turing.pairEncode x y`.

A head on the virtual input is described by its segment `s` and a *track position*
(`TPos`): the left end of the segment (the cell before its first rendered bit), a cell
`c` of the underlying word together with a parity bit (which of the two copies, for a
doubled segment), or its right end (the cell after its last rendered bit). The left end of
segment `s + 1` is the last separator bit of segment `s`'s separator and its right end the
first; the left end of segment `0` and the right end of the last segment are the two
blank cells around the virtual input.

## Main definitions

* `Complexity.LogProg.vword` — the virtual input of a segment list.
* `Complexity.LogProg.vpos` — the (shifted, as in `Turing.Cfg.inputPos`) virtual position
  of a track position.
* `Complexity.LogProg.tmove` — the track position after a head move.

## Main results

* `Complexity.LogProg.vpos_tmove` — `tmove` implements the clamped input-head move of the
  machine model on the virtual input.
* `Complexity.LogProg.inputSymbol_vpos` — the symbol read at a track position.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

-- The doubling `Turing.dbl`, `Turing.getElem?_dbl` and `Turing.pairEncode_eq_dbl` live in
-- `TCSlib.Complexity.TuringMachine.Encoding`.

/-- A segment of a virtual input: a word, and whether it is rendered doubled. -/
abbrev Seg := List Bool × Bool

/-- The rendering of a segment. -/
def render (s : Seg) : List Bool := if s.2 then dbl s.1 else s.1

/-- The length of the rendering of a segment. -/
def rlen (s : Seg) : ℕ := if s.2 then 2 * s.1.length else s.1.length

/-- A doubled segment renders to twice its word's length. -/
@[simp] lemma rlen_true (w : List Bool) : rlen (w, true) = 2 * w.length := rfl
/-- A plain segment renders to its word's length. -/
@[simp] lemma rlen_false (w : List Bool) : rlen (w, false) = w.length := rfl

/-- The rendering of a segment has length `rlen`. -/
@[simp] lemma length_render (s : Seg) : (render s).length = rlen s := by
  unfold render rlen; split <;> simp

/-- The virtual input of a nonempty segment list: the renderings joined by `[false, true]`. -/
def vword : List Seg → List Bool
  | [] => []
  | [s] => render s
  | s :: t :: rest => render s ++ [false, true] ++ vword (t :: rest)

/-- The offset of segment `i` in the virtual input. -/
def off : List Seg → ℕ → ℕ
  | _, 0 => 0
  | [], _ + 1 => 0
  | s :: rest, i + 1 => rlen s + 2 + off rest i

/-- Segment `i`, with a default beyond the list. -/
def seg (segs : List Seg) (i : ℕ) : Seg := segs.getD i ([], false)

/-- The segment `0` of `s :: rest` is `s`. -/
@[simp] lemma seg_cons_zero (s : Seg) (rest : List Seg) : seg (s :: rest) 0 = s := rfl
/-- The segment `i + 1` of `s :: rest` is segment `i` of `rest`. -/
@[simp] lemma seg_cons_succ (s : Seg) (rest : List Seg) (i : ℕ) :
    seg (s :: rest) (i + 1) = seg rest i := rfl

/-- The next offset is past the segment and its separator. -/
lemma off_succ (segs : List Seg) (i : ℕ) (hi : i + 1 < segs.length) :
    off segs (i + 1) = off segs i + rlen (seg segs i) + 2 := by
  induction segs generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
    cases i with
    | zero => simp [off]
    | succ i =>
      simp only [off, seg_cons_succ]
      rw [ih i (by simp at hi; omega)]
      ring

/-- The virtual input ends with the last segment. -/
lemma length_vword (segs : List Seg) (h : segs ≠ []) :
    (vword segs).length = off segs (segs.length - 1) + rlen (seg segs (segs.length - 1)) := by
  induction segs with
  | nil => exact absurd rfl h
  | cons s rest ih =>
    cases rest with
    | nil => simp [vword, off, seg]
    | cons t rest' =>
      have := ih (by simp)
      simp only [vword, List.length_append, length_render, List.length_cons] at this ⊢
      simp only [Nat.add_sub_cancel, off, seg_cons_succ]
      simp only [Nat.add_sub_cancel] at this
      rw [this]
      cases rest'.length <;> simp [off]; ring

/-- Inside segment `i`, the virtual input reads the segment's rendering: cell `off segs i + k` holds
letter `k` of `render (seg segs i)`.

**Proof sketch.** Induction on the segment list: segment `0` is the start of the virtual input,
and segment `i + 1` is segment `i` of the rest after the first rendering and its separator,
whose length shifts the offset. -/
lemma getElem?_vword_seg (segs : List Seg) (i k : ℕ) (hi : i < segs.length)
    (hk : k < rlen (seg segs i)) :
    (vword segs)[off segs i + k]? = (render (seg segs i))[k]? := by
  induction segs generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
    cases rest with
    | nil =>
      have : i = 0 := by simp at hi; omega
      subst this; simp [vword, off]
    | cons t rest' =>
      cases i with
      | zero =>
        simp only [vword, off, seg_cons_zero, Nat.zero_add] at hk ⊢
        rw [List.append_assoc, List.getElem?_append_left (by simpa using hk)]
      | succ i =>
        simp only [vword, off, seg_cons_succ] at hk ⊢
        rw [show rlen s + 2 + off (t :: rest') i + k = (render s ++ [false, true]).length +
          (off (t :: rest') i + k) by simp; ring, List.getElem?_append_right (by simp)]
        simp only [Nat.add_sub_cancel_left]
        exact ih i (by simp at hi ⊢; omega) hk

/-- The separator `0 1` after segment `i` of a virtual input sits right after that segment's
rendering.

**Proof sketch.** Induction on the segment list: for `i = 0` the virtual input is the first
rendering followed by `[false, true]`; for `i + 1` drop the first rendering and its separator,
shifting the offsets by their length. -/
lemma getElem?_vword_sep (segs : List Seg) (i : ℕ) (hi : i + 1 < segs.length) :
    (vword segs)[off segs i + rlen (seg segs i)]? = some false ∧
    (vword segs)[off segs i + rlen (seg segs i) + 1]? = some true := by
  induction segs generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
    cases rest with
    | nil => simp at hi
    | cons t rest' =>
      cases i with
      | zero =>
        simp only [vword, off, seg_cons_zero, Nat.zero_add]
        constructor
        · rw [List.append_assoc, List.getElem?_append_right (by simp)]; simp
        · rw [List.append_assoc, List.getElem?_append_right (by simp)]; simp
      | succ i =>
        simp only [vword, off, seg_cons_succ]
        have h := ih i (by simp at hi ⊢; omega)
        constructor
        · rw [show rlen s + 2 + off (t :: rest') i + rlen (seg (t :: rest') i) =
            (render s ++ [false, true]).length + (off (t :: rest') i +
              rlen (seg (t :: rest') i)) by simp; ring, List.getElem?_append_right (by simp)]
          simpa using h.1
        · rw [show rlen s + 2 + off (t :: rest') i + rlen (seg (t :: rest') i) + 1 =
            (render s ++ [false, true]).length + (off (t :: rest') i +
              rlen (seg (t :: rest') i) + 1) by simp; ring,
            List.getElem?_append_right (by simp)]
          simpa using h.2

/-! ## Track positions -/

/-- A position of a head on a segment: its left end, a cell of the underlying word with a
parity (the copy, for doubled segments), or its right end. -/
inductive TPos where
  | left
  | cell (c : ℕ) (p : Bool)
  | right
  deriving DecidableEq

/-- The underlying word length of segment `s`. -/
def wlen (segs : List Seg) (s : ℕ) : ℕ := (seg segs s).1.length

/-- A track position is valid when its cell lies in the word. -/
def TPos.Valid (segs : List Seg) (s : ℕ) : TPos → Prop
  | .cell c _ => c < wlen segs s
  | _ => True

/-- The rendered offset of a cell inside its segment. -/
def cellOff (segs : List Seg) (s c : ℕ) (p : Bool) : ℕ :=
  if (seg segs s).2 then 2 * c + p.toNat else c

/-- The virtual position (`inputPos`-style: `0` is the left blank, cell `j` of the virtual
input is position `j + 1`) of a track position. -/
def vpos (segs : List Seg) (s : ℕ) : TPos → ℕ
  | .left => off segs s
  | .cell c p => off segs s + 1 + cellOff segs s c p
  | .right => off segs s + 1 + rlen (seg segs s)

/-- The rendered offset of a cell of a segment's word lies within the segment's rendering. -/
lemma cellOff_lt (segs : List Seg) (s c : ℕ) (p : Bool) (hc : c < wlen segs s) :
    cellOff segs s c p < rlen (seg segs s) := by
  unfold cellOff rlen
  unfold wlen at hc
  generalize seg segs s = sg at *
  obtain ⟨w, d⟩ := sg
  cases d <;> cases p <;> simp at hc ⊢ <;> omega

/-- The track position after a head move by `m` (`tmove`'s first component is the new
segment). -/
def tmove (segs : List Seg) (s : ℕ) : TPos → SignType → ℕ × TPos
  | tp, .zero => (s, tp)
  | .cell c p, .pos =>
    if (seg segs s).2 ∧ p = false then (s, .cell c true)
    else if c + 1 < wlen segs s then (s, .cell (c + 1) false) else (s, .right)
  | .cell c p, .neg =>
    if (seg segs s).2 ∧ p = true then (s, .cell c false)
    else if c = 0 then (s, .left) else (s, .cell (c - 1) true)
  | .right, .pos => if s + 1 < segs.length then (s + 1, .left) else (s, .right)
  | .right, .neg => if wlen segs s = 0 then (s, .left) else (s, .cell (wlen segs s - 1) true)
  | .left, .pos => if wlen segs s = 0 then (s, .right) else (s, .cell 0 false)
  | .left, .neg => if s = 0 then (s, .left) else (s - 1, .right)

/-- `tmove` preserves validity and the segment bound. -/
lemma tmove_valid (segs : List Seg) (s : ℕ) (hs : s < segs.length) (tp : TPos)
    (htp : tp.Valid segs s) (m : SignType) :
    (tmove segs s tp m).1 < segs.length ∧
      (tmove segs s tp m).2.Valid segs (tmove segs s tp m).1 := by
  cases m <;> cases tp <;> simp only [tmove] <;> (try split_ifs) <;>
    simp_all [TPos.Valid] <;> omega

/-- The virtual input's length in terms of the last segment. -/
lemma vpos_right_last (segs : List Seg) (s : ℕ) (hs : s + 1 = segs.length) :
    vpos segs s .right = (vword segs).length + 1 := by
  rw [length_vword segs (by rintro rfl; simp at hs)]
  simp only [vpos, show segs.length - 1 = s by omega]
  ring

/-- Every segment ends inside the virtual input. -/
lemma off_add_rlen_le (segs : List Seg) (j : ℕ) (hj : j < segs.length) :
    off segs j + rlen (seg segs j) ≤ (vword segs).length := by
  induction segs generalizing j with
  | nil => simp at hj
  | cons s rest ih =>
    cases rest with
    | nil =>
      have : j = 0 := by simp at hj; omega
      subst this; simp [vword, off]
    | cons t rest' =>
      cases j with
      | zero => simp [vword, off]
      | succ j =>
        have := ih j (by simp at hj ⊢; omega)
        simp only [vword, off, seg_cons_succ, List.length_append, length_render,
          List.length_cons, List.length_nil] at this ⊢
        omega

/-- The clamped input move, numerically. -/
lemma moveInputPos_val (N p : ℕ) (hp : p < N + 2) (m : SignType) :
    (moveInputPos (n := N) ⟨p, hp⟩ m).val =
      match m with
      | .zero => p
      | .pos => min (p + 1) (N + 1)
      | .neg => p - 1 := by
  cases m <;> simp only [moveInputPos, SignType.zero_eq_zero, SignType.coe_zero,
    SignType.pos_eq_one, SignType.coe_one, SignType.neg_eq_neg_one, SignType.coe_neg_one] <;>
    split <;> simp_all <;> omega

/-- `tmove` implements the clamped head move: the virtual position after the move is the
old one moved by `m`, clamped to `[0, |V| + 1]`.

**Proof sketch.** Case analysis on the track position and the move. Inside a word the
rendered offset changes by one (doubled segments switch copies before cells). From an end
of a segment the head passes to the neighbouring separator bit, which is the opposite end
of the neighbouring segment (`off_succ`); the outermost ends clamp (`vpos_right_last`). -/
lemma vpos_tmove (segs : List Seg) (s : ℕ) (hs : s < segs.length) (tp : TPos)
    (htp : tp.Valid segs s) (m : SignType) (hlt : vpos segs s tp < (vword segs).length + 2) :
    vpos segs (tmove segs s tp m).1 (tmove segs s tp m).2 =
      (moveInputPos (n := (vword segs).length) ⟨vpos segs s tp, hlt⟩ m).val := by
  rw [moveInputPos_val]
  have F1 := off_add_rlen_le segs s hs
  have F2 : s + 1 < segs.length → off segs (s + 1) = off segs s + rlen (seg segs s) + 2 ∧
      off segs (s + 1) + rlen (seg segs (s + 1)) ≤ (vword segs).length := fun h =>
    ⟨off_succ segs s h, off_add_rlen_le segs (s + 1) h⟩
  have F3 : s + 1 = segs.length → off segs s + rlen (seg segs s) = (vword segs).length := by
    intro h; have := vpos_right_last segs s h; simp only [vpos] at this; omega
  have F4 : 0 < s → off segs s = off segs (s - 1) + rlen (seg segs (s - 1)) + 2 := by
    intro h
    have := off_succ segs (s - 1) (by omega)
    rwa [Nat.sub_add_cancel h] at this
  have F5 : 0 < s → off segs (s - 1) + rlen (seg segs (s - 1)) ≤ (vword segs).length :=
    fun h => off_add_rlen_le segs (s - 1) (by omega)
  unfold TPos.Valid at htp
  generalize hsg : seg segs s = sg at *
  obtain ⟨w, d⟩ := sg
  unfold wlen at htp
  rw [hsg] at htp
  dsimp only at htp
  cases m with
  | zero => simp only [tmove]
  | pos =>
    cases tp with
    | left =>
      simp only [tmove, wlen, hsg]
      split_ifs with h <;>
        cases d <;> simp only [vpos, cellOff, rlen_true, rlen_false, hsg, ↓reduceIte, Bool.false_eq_true,
          Bool.toNat_false] at * <;> omega
    | cell c p =>
      simp only [tmove, wlen, hsg]
      split_ifs with h1 h2 <;>
        cases d <;> cases p <;> simp only [vpos, cellOff, rlen_true, rlen_false, hsg, ↓reduceIte,
          Bool.false_eq_true, Bool.true_eq_false, Bool.toNat_false, Bool.toNat_true, and_true,
          and_false, not_true, not_false_eq_true] at * <;> omega
    | right =>
      simp only [tmove]
      split_ifs with h
      · obtain ⟨e1, e2⟩ := F2 h
        simp only [vpos]
        rw [e1]
        cases d <;> simp only [vpos, rlen_true, rlen_false, hsg] at * <;>
          omega
      · have := F3 (by omega)
        cases d <;> simp only [vpos, rlen_true, rlen_false, hsg] at * <;>
          omega
  | neg =>
    cases tp with
    | left =>
      simp only [tmove]
      split_ifs with h
      · subst h; simp [vpos, off]
      · have e := F4 (by omega)
        simp only [vpos] at hlt ⊢
        rw [e]
        omega
    | cell c p =>
      simp only [tmove, hsg]
      split_ifs with h1 h2 <;>
        cases d <;> cases p <;> simp only [vpos, cellOff, rlen_true, rlen_false, hsg, ↓reduceIte,
          Bool.false_eq_true, Bool.toNat_false, Bool.toNat_true, and_true,
          and_false, not_true, not_false_eq_true] at * <;> omega
    | right =>
      simp only [tmove, wlen, hsg]
      split_ifs with h <;>
        cases d <;> simp only [vpos, cellOff, rlen_true, rlen_false, hsg, ↓reduceIte, Bool.false_eq_true,
          Bool.toNat_true] at * <;> omega

/-- The symbol of the virtual input at a track position. -/
def vsym (segs : List Seg) (s : ℕ) : TPos → Option Bool
  | .left => if s = 0 then none else some true
  | .cell c _ => (seg segs s).1[c]?
  | .right => if s + 1 < segs.length then some false else none

/-- The input symbol read at a configuration whose input head is at a track position is
`vsym`.

**Proof sketch.** Unfold the input symbol at position `vpos segs s tp`. A cell position falls
inside segment `s`'s rendering (`cellOff_lt`), giving its letter. A left or right blank position
falls on the end marker, on the separator `0 1` (`getElem?_vword_sep`) or past the end, which is
`vsym`'s case split. -/
lemma inputSymbol_vpos {k : ℕ} {S : Type} (segs : List Seg) (s : ℕ) (hs : s < segs.length)
    (tp : TPos) (htp : tp.Valid segs s) (cfg : Cfg k Bool S (vword segs))
    (hpos : cfg.inputPos.val = vpos segs s tp) : cfg.inputSymbol = vsym segs s tp := by
  have hgen : ∀ j, cfg.inputPos.val = j + 1 → j ≤ (vword segs).length →
      cfg.inputSymbol = (vword segs)[j]? := fun j hj hl => FinTM.inputSymbol_at cfg j hl hj
  have hlt := cfg.inputPos.isLt
  cases tp with
  | left =>
    simp only [vpos, vsym] at hpos ⊢
    split_ifs with h
    · subst h
      have hz : cfg.inputPos = 0 := Fin.ext (by simpa [off] using hpos)
      simp [Cfg.inputSymbol, hz]
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
      rw [off_succ segs j hs] at hpos
      rw [hgen (off segs j + rlen (seg segs j) + 1) (by omega) (by omega)]
      exact (getElem?_vword_sep segs j hs).2
  | cell c p =>
    simp only [TPos.Valid, wlen] at htp
    simp only [vpos, vsym] at hpos ⊢
    have hc := cellOff_lt segs s c p htp
    rw [hgen (off segs s + cellOff segs s c p) (by omega) (by omega),
      getElem?_vword_seg segs s _ hs hc]
    unfold cellOff render
    split
    · exact (getElem?_dbl _ c htp p).trans (List.getElem?_eq_getElem htp).symm
    · rfl
  | right =>
    simp only [vpos, vsym] at hpos ⊢
    split_ifs with h
    · rw [hgen (off segs s + rlen (seg segs s)) (by omega) (by omega)]
      exact (getElem?_vword_sep segs s h).1
    · have hl : s + 1 = segs.length := by omega
      have := vpos_right_last segs s hl
      simp only [vpos] at this
      have hz : cfg.inputPos.val = (vword segs).length + 1 := by omega
      have hne : cfg.inputPos ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
      simp [Cfg.inputSymbol, hne, hz]

end Complexity.LogProg
