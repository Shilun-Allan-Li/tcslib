/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyTableauCorrect
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One step of the configuration tableau

The local rules of the *configuration tableau* of an arbitrary (not necessarily
oblivious) machine: the circuit-friendly form of one step of `Turing.MultiTapeTM.step`.
At every step the tableau records, for each work tape `τ` and each cell `z` of a window
`[−T, T]`, a **cell block** (is the head here?, the cell's content, and a running
"symbol under the head, if the head is at or left of `z`" value); for each input position
`p` an **input block** (is the input head here?, and the running symbol); and the
snapshot.  This file defines the finite functions computing these blocks
(`Complexity.cfgF`) and proves that, fed with the true values at the previous step, they
produce the true values at the next step.

This is a standard configuration tableau — not the construction of [AB09], which proves
Thm 6.6 only through oblivious machines; it adapts the 6.6 construction (one constant-size
gadget per tableau entry) by tracking every cell of a window instead of the oblivious
schedule.  It is used for machines that are not oblivious, such as advice machines run on
pairs (`CircuitComplexity/PAdviceSubsetPPoly`).

## Main definitions

* `Complexity.CfgKind` — the three kinds of instructions: work cell of tape `τ`, input
  cell, snapshot.
* `Complexity.cellHead`, `Complexity.cellContent`, `Complexity.inHead` — how a head bit
  and a cell content change in one step.
* `Complexity.cfgF` — the finite functions of the three kinds.
* `Complexity.cellExp`, `Complexity.inpExp`, `Complexity.snapExp` — the true blocks.

## Main results

* `Complexity.cfgF_cell_zero`, `Complexity.cfgF_cell_succ`, `Complexity.cfgF_inp_zero`,
  `Complexity.cfgF_inp_succ`, `Complexity.cfgF_snap` — one step of the tableau is
  correct.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, proof of Theorem 6.6; §2.3.4.)
-/

namespace Complexity

open Turing BoolCircuit

namespace CfgTableau

/-! ## Bits for an optional symbol -/

/-- An optional bit as two bits: present, value. -/
def optBits (o : Option Bool) : List Bool := [o.isSome, o.getD false]

/-- Decode two bits (present, value) to an optional bit. -/
def optOf (s v : Bool) : Option Bool := if s then some v else none

/-- Decoding the two bits of an optional bit gives it back. -/
@[simp] theorem optOf_isSome_getD (o : Option Bool) : optOf o.isSome (o.getD false) = o := by
  cases o <;> rfl

/-- Two bits with the present flag unset decode to nothing. -/
@[simp] theorem optOf_false (v : Bool) : optOf false v = none := rfl

end CfgTableau

open CfgTableau

variable (M : FinTM Bool)

/-! ## Local rules -/

/-- The kinds of instructions of the configuration tableau: `some (some τ)` a cell of work
tape `τ`, `some none` an input cell, `none` the snapshot. -/
abbrev CfgKind (k : ℕ) : Type := Option (Option (Fin k))

/-- The head bit of a work cell after one step, from the snapshot and the head bits of the
cell and its two neighbours before it: the head moves by the transition's move. -/
def cellHead (s : Snapshot M) (τ : Fin M.k) (hl hm hr : Bool) : Bool :=
  match s.1 with
  | none => hm
  | some q =>
    match ((M.tm.tr q s.2.1 s.2.2).workTapes τ).2 with
    | .pos => hl
    | .zero => hm
    | .neg => hr

/-- The content of a work cell after one step: rewritten (or kept, if the transition writes
nothing) when the head is on it and the machine is live. -/
def cellContent (s : Snapshot M) (τ : Fin M.k) (hm : Bool) (cont : Option Bool) :
    Option Bool :=
  match s.1 with
  | none => cont
  | some q => if hm then ((M.tm.tr q s.2.1 s.2.2).workTapes τ).1.getD cont else cont

/-- The input-head bit of a position after one step, from the snapshot, the boundary flags
of the position and the head bits of the position and its two neighbours: the head moves
by the transition's move, clamped at the two boundary cells. -/
def inHead (s : Snapshot M) (isL isR hl hm hr : Bool) : Bool :=
  match s.1 with
  | none => hm
  | some q =>
    match (M.tm.tr q s.2.1 s.2.2).inputTape with
    | .pos => hl || (isR && hm)
    | .zero => hm
    | .neg => hr || (isL && hm)

/-- **The finite functions of the configuration tableau.**

* Work cell of tape `τ`, sources `[isZero, isOrigin, hl, sl, vl, hm, sm, vm, hr, sr, vr,
  cs, cv] ++ prev`: the head bit and content (from the neighbours' head bits and own
  content, `cellHead`/`cellContent`; at time `0` the head is at the origin and the cell
  blank), then the running symbol (`cs, cv` being the running symbol of the cell to the
  left).
* Input cell, sources `[isZero, isOne, isL, isR, ps, pv, hl, hm, hr, cs, cv] ++ prev`: the
  head bit (`inHead`; at time `0` the head is at position `1`), then the running symbol
  (`ps, pv` being this cell's input symbol).
* Snapshot, sources `[isZero, acc, is, iv] ++ (work running symbols) ++ prev`: the state
  steps by `stepState` (or is the initial state), the read symbols are the running symbols
  at the right end of each window, and the accumulator gains the emission of the previous
  snapshot. -/
noncomputable def cfgF : CfgKind M.k → List Bool → List Bool
  | some (some τ), l =>
    let b := fun i => l.getD i false
    let prev := snapDecode M ((l.drop 13).take (snapWidth M))
    let head := if b 0 then b 1 else cellHead M prev τ (b 2) (b 5) (b 8)
    let cont := if b 0 then none else cellContent M prev τ (b 5) (optOf (b 6) (b 7))
    let chain := if head then cont else optOf (b 11) (b 12)
    head :: (optBits cont ++ optBits chain)
  | some none, l =>
    let b := fun i => l.getD i false
    let prev := snapDecode M ((l.drop 11).take (snapWidth M))
    let head := if b 0 then b 1 else inHead M prev (b 2) (b 3) (b 6) (b 7) (b 8)
    let chain := if head then optOf (b 4) (b 5) else optOf (b 9) (b 10)
    head :: optBits chain
  | none, l =>
    let b := fun i => l.getD i false
    let prev := snapDecode M ((l.drop (4 + 2 * M.k)).take (snapWidth M))
    let new : Snapshot M :=
      (if b 0 then some M.tm.q₀ else stepState M prev, optOf (b 2) (b 3),
        fun τ => optOf (b (4 + 2 * τ)) (b (5 + 2 * τ)))
    snapEncode M new ++ [if b 0 then false else b 1 || decide (emitted M prev = some true)]

/-! ## The true blocks -/

namespace CfgTableau

/-- The configuration after `t` steps on the (virtual) input `w`. -/
abbrev cfgAt (w : List Bool) (t : ℕ) : Cfg M.k Bool M.State w :=
  M.tm.runFrom (M.tm.initCfg w) t

end CfgTableau

/-- The running symbol of work tape `τ` at cell `z`: the symbol under the head if the
head is at or left of `z`, else nothing. -/
def workChain (w : List Bool) (t : ℕ) (τ : Fin M.k) (z : ℤ) : Option Bool :=
  if (cfgAt M w t).workTapePos τ ≤ z then (cfgAt M w t).workTapeSymbols τ else none

/-- The true block of cell `z = r − T` of work tape `τ` at step `t`. -/
def cellExp (w : List Bool) (T t : ℕ) (τ : Fin M.k) (r : ℕ) : List Bool :=
  decide ((cfgAt M w t).workTapePos τ = (r : ℤ) - T) ::
    (optBits ((cfgAt M w t).workTapes τ ((r : ℤ) - T)) ++
      optBits (workChain M w t τ ((r : ℤ) - T)))

/-- The running input symbol at position `p`: the symbol under the input head if the head
is at or left of `p`, else nothing. -/
def inpChain (w : List Bool) (t p : ℕ) : Option Bool :=
  if ((cfgAt M w t).inputPos : ℕ) ≤ p then (cfgAt M w t).inputSymbol else none

/-- The true block of input position `p` at step `t`. -/
def inpExp (w : List Bool) (t p : ℕ) : List Bool :=
  decide (((cfgAt M w t).inputPos : ℕ) = p) :: optBits (inpChain M w t p)

/-- The true snapshot block at step `t`: the snapshot's encoding and the accumulator. -/
noncomputable def snapExp (w : List Bool) (t : ℕ) : List Bool :=
  snapEncode M (snapshotAt M w t) ++ [tableauAccepted M w t]

/-! ## Facts about runs -/

/-- A work head is within distance `t` of the origin after `t` steps. -/
theorem abs_workTapePos_le (w : List Bool) (t : ℕ) (τ : Fin M.k) :
    |(cfgAt M w t).workTapePos τ| ≤ t := by
  induction t with
  | zero => simp [cfgAt, MultiTapeTM.runFrom_zero, Cfg.init]
  | succ t ih =>
    have h := MultiTapeTM.workTapePos_step_le (tm := M.tm) (cfgAt M w t) τ
    simp only [cfgAt, MultiTapeTM.runFrom_succ_eq_step'] at h ih ⊢
    rw [abs_le] at h ih ⊢
    push_cast
    constructor <;> linarith [h.1, h.2, ih.1, ih.2]

/-- The input symbol under the head, as a function of the head position. -/
theorem inputSymbol_eq_inputBitAt {w : List Bool} (c : Cfg M.k Bool M.State w) :
    c.inputSymbol = inputBitAt w c.inputPos := by
  by_cases h0 : (c.inputPos : ℕ) = 0
  · have hp : c.inputPos = 0 := Fin.val_eq_zero_iff.mp h0
    simp [Cfg.inputSymbol, hp, inputBitAt]
  · have hb := c.inputPos.isLt
    rw [inputBitAt, if_neg h0]
    exact FinTM.inputSymbol_at c ((c.inputPos : ℕ) - 1) (by omega) (by omega)

/-- **One step of a work cell** (any machine): the head bit and content of cell `z` after
a step are `cellHead` and `cellContent` of the snapshot and the head bits and content
before it.

**Proof sketch.** A halted configuration is fixed.  A live step applies the action
selected by the snapshot: the head moves by the action's move, so it is at `z` after the
step iff it was at `z − 1`, `z` or `z + 1` for a move `+1`, `0` or `−1`; and only the old
head cell is rewritten (`Turing.Action.apply_workTapes`). -/
private theorem cell_step {w : List Bool} (c : Cfg M.k Bool M.State w) (τ : Fin M.k) (z : ℤ) :
    decide ((M.tm.step c).workTapePos τ = z) =
      cellHead M (c.state, c.inputSymbol, c.workTapeSymbols) τ
        (decide (c.workTapePos τ = z - 1)) (decide (c.workTapePos τ = z))
        (decide (c.workTapePos τ = z + 1)) ∧
    (M.tm.step c).workTapes τ z =
      cellContent M (c.state, c.inputSymbol, c.workTapeSymbols) τ
        (decide (c.workTapePos τ = z)) (c.workTapes τ z) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [cellHead, cellContent]
  | some q =>
    simp only [cellHead, cellContent]
    constructor
    · simp only [Action.apply]
      split <;> rename_i heq <;> simp only [heq] <;> simp [SignType.cast] <;> omega
    · rw [Action.apply_workTapes]
      by_cases hz : z = c.workTapePos τ
      · subst hz
        simp [Cfg.workTapeSymbols]
      · rw [Function.update_of_ne hz]
        simp [Ne.symm hz]

private theorem moveInputPos_pos_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos SignType.pos : ℕ) = min ((pos : ℕ) + 1) (n + 1) := by
  have := pos.isLt
  unfold moveInputPos
  dsimp only
  split <;> rename_i h <;> simp [SignType.cast] at h ⊢ <;> omega

private theorem moveInputPos_neg_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos SignType.neg : ℕ) = (pos : ℕ) - 1 := by
  have := pos.isLt
  unfold moveInputPos
  dsimp only
  split <;> rename_i h <;> simp [SignType.cast] at h ⊢ <;> omega

/-- **One step of an input cell** (any machine): the input-head bit of position `p` after a
step is `inHead` of the snapshot, the boundary flags and the head bits before it.

**Proof sketch.** A halted configuration is fixed.  For a live step compute the clamped
move `moveInputPos` for each of the three moves: a move `+1` lands on `p` from `p − 1`,
or stays at the right end `N + 1`; a move `−1` lands on `p` from `p + 1`, or stays at `0`.
Arithmetic on positions `≤ N + 1` then finishes. -/
private theorem inp_step {w : List Bool} (c : Cfg M.k Bool M.State w) {p : ℕ}
    (hp : p ≤ w.length + 1) :
    decide (((M.tm.step c).inputPos : ℕ) = p) =
      inHead M (c.state, c.inputSymbol, c.workTapeSymbols) (decide (p = 0))
        (decide (p = w.length + 1)) (decide (1 ≤ p ∧ (c.inputPos : ℕ) = p - 1))
        (decide ((c.inputPos : ℕ) = p)) (decide ((c.inputPos : ℕ) = p + 1)) := by
  unfold MultiTapeTM.step
  have hb := c.inputPos.isLt
  cases hs : c.state with
  | none => simp [inHead]
  | some q =>
    simp only [inHead, Action.apply]
    split <;> rename_i heq <;> simp only [heq]
    · rw [moveInputPos_pos_val, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.min_def]
      generalize (c.inputPos : ℕ) = ip at *
      split_ifs <;> omega
    · rw [show SignType.zero = 0 from rfl, moveInputPos_zero]
    · rw [moveInputPos_neg_val, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
      generalize (c.inputPos : ℕ) = ip at *
      omega

/-! ## The local rules are correct -/

/-- The accumulator recurrence: some step `< t + 1` emitted `1` iff some step `< t` did or
step `t` did. -/
theorem tableauAccepted_succ (w : List Bool) (t : ℕ) :
    tableauAccepted M w (t + 1) =
      (tableauAccepted M w t || decide (emitted M (snapshotAt M w t) = some true)) := by
  rw [Bool.eq_iff_iff]
  simp only [tableauAccepted, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, he⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact Or.inl ⟨s, hs, he⟩
    · exact Or.inr he
  · rintro (⟨s, hs, he⟩ | he)
    · exact ⟨s, by omega, he⟩
    · exact ⟨t, by omega, he⟩

/-- The running symbol recurrence: at cell `z` it is the content if the head is here, and
otherwise the running symbol of cell `z − 1`. -/
theorem workChain_eq (w : List Bool) (t : ℕ) (τ : Fin M.k) (z : ℤ) :
    workChain M w t τ z =
      if (cfgAt M w t).workTapePos τ = z then (cfgAt M w t).workTapes τ z
        else workChain M w t τ (z - 1) := by
  unfold workChain
  by_cases h : (cfgAt M w t).workTapePos τ = z
  · rw [if_pos h.le, if_pos h, Cfg.workTapeSymbols, h]
  · rw [if_neg h]
    by_cases h' : (cfgAt M w t).workTapePos τ ≤ z - 1
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]

/-- The running input-symbol recurrence. -/
theorem inpChain_eq (w : List Bool) (t p : ℕ) :
    inpChain M w t p =
      if ((cfgAt M w t).inputPos : ℕ) = p then inputBitAt w p
        else if p = 0 then none else inpChain M w t (p - 1) := by
  unfold inpChain
  rw [inputSymbol_eq_inputBitAt]
  by_cases h : ((cfgAt M w t).inputPos : ℕ) = p
  · rw [if_pos h.le, if_pos h, h]
  · rw [if_neg h]
    by_cases hp : p = 0
    · rw [if_pos hp, if_neg (by omega)]
    · rw [if_neg hp]
      by_cases h' : ((cfgAt M w t).inputPos : ℕ) ≤ p - 1
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega)]

/-- A work cell at time `0`: the head is at the origin and every cell is blank. -/
theorem cfgF_cell_zero (w : List Bool) (τ : Fin M.k) (z : ℤ) (l : List Bool)
    (h0 : l.getD 0 false = true) (h1 : l.getD 1 false = decide (z = 0))
    (hcs : l.getD 11 false = false) :
    cfgF M (some (some τ)) l = decide ((cfgAt M w 0).workTapePos τ = z) ::
      (optBits ((cfgAt M w 0).workTapes τ z) ++ optBits (workChain M w 0 τ z)) := by
  simp only [cfgF, h0, h1, hcs, if_true, optOf_false]
  simp [cfgAt, MultiTapeTM.runFrom_zero, Cfg.init, workChain, Cfg.workTapeSymbols, optBits,
    eq_comm]

/-- **A work cell after a step**: fed with the snapshot, the neighbours' head bits, its own
content and the running symbol on its left, the cell rule returns the true block.

**Proof sketch.** Rewrite the decoded inputs with the hypotheses.  The head bit and
the content are the private lemma `cell_step` for the step from `t` to `t + 1`, and the running
symbol follows `Complexity.workChain_eq`. -/
theorem cfgF_cell_succ (w : List Bool) (t : ℕ) (τ : Fin M.k) (z : ℤ) (l : List Bool)
    (h0 : l.getD 0 false = false)
    (hprev : snapDecode M ((l.drop 13).take (snapWidth M)) = snapshotAt M w t)
    (hl : l.getD 2 false = decide ((cfgAt M w t).workTapePos τ = z - 1))
    (hm : l.getD 5 false = decide ((cfgAt M w t).workTapePos τ = z))
    (hr : l.getD 8 false = decide ((cfgAt M w t).workTapePos τ = z + 1))
    (hs : l.getD 6 false = ((cfgAt M w t).workTapes τ z).isSome)
    (hv : l.getD 7 false = ((cfgAt M w t).workTapes τ z).getD false)
    (hcs : l.getD 11 false = (workChain M w (t + 1) τ (z - 1)).isSome)
    (hcv : l.getD 12 false = (workChain M w (t + 1) τ (z - 1)).getD false) :
    cfgF M (some (some τ)) l = decide ((cfgAt M w (t + 1)).workTapePos τ = z) ::
      (optBits ((cfgAt M w (t + 1)).workTapes τ z) ++
        optBits (workChain M w (t + 1) τ z)) := by
  have hstep := cell_step M (cfgAt M w t) τ z
  have hsnap : snapshotAt M w t = ((cfgAt M w t).state, (cfgAt M w t).inputSymbol,
      (cfgAt M w t).workTapeSymbols) := rfl
  have hrun : cfgAt M w (t + 1) = M.tm.step (cfgAt M w t) :=
    MultiTapeTM.runFrom_succ_eq_step'
  simp only [cfgF, h0, hprev, hl, hm, hr, hs, hv, hcs, hcv, Bool.false_eq_true, if_false,
    optOf_isSome_getD]
  rw [hsnap, ← hstep.1, ← hstep.2, ← hrun, workChain_eq M w (t + 1) τ z]
  by_cases h : (cfgAt M w (t + 1)).workTapePos τ = z <;> simp [h]

/-- An input cell at time `0`: the head is at position `1`. -/
theorem cfgF_inp_zero (w : List Bool) (p : ℕ) (l : List Bool)
    (h0 : l.getD 0 false = true) (h1 : l.getD 1 false = decide (p = 1))
    (hps : l.getD 4 false = (inputBitAt w p).isSome)
    (hpv : l.getD 5 false = (inputBitAt w p).getD false)
    (hcs : l.getD 9 false = (if p = 0 then none else inpChain M w 0 (p - 1)).isSome)
    (hcv : l.getD 10 false = (if p = 0 then none else inpChain M w 0 (p - 1)).getD false) :
    cfgF M (some none) l = decide (((cfgAt M w 0).inputPos : ℕ) = p) ::
      optBits (inpChain M w 0 p) := by
  have hpos : ((cfgAt M w 0).inputPos : ℕ) = 1 := by
    simp [cfgAt, MultiTapeTM.runFrom_zero, Cfg.init]
  simp only [cfgF, h0, h1, hps, hpv, hcs, hcv, if_true, optOf_isSome_getD]
  rw [inpChain_eq M w 0 p, hpos]
  by_cases h : 1 = p
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **An input cell after a step**.

**Proof sketch.** The head bit is the private lemma `inp_step` for the step from `t` to
`t + 1`, and the running symbol follows `Complexity.inpChain_eq`. -/
theorem cfgF_inp_succ (w : List Bool) (t p : ℕ) (hp : p ≤ w.length + 1) (l : List Bool)
    (h0 : l.getD 0 false = false)
    (hprev : snapDecode M ((l.drop 11).take (snapWidth M)) = snapshotAt M w t)
    (hL : l.getD 2 false = decide (p = 0)) (hR : l.getD 3 false = decide (p = w.length + 1))
    (hps : l.getD 4 false = (inputBitAt w p).isSome)
    (hpv : l.getD 5 false = (inputBitAt w p).getD false)
    (hl : l.getD 6 false = decide (1 ≤ p ∧ ((cfgAt M w t).inputPos : ℕ) = p - 1))
    (hm : l.getD 7 false = decide (((cfgAt M w t).inputPos : ℕ) = p))
    (hr : l.getD 8 false = decide (((cfgAt M w t).inputPos : ℕ) = p + 1))
    (hcs : l.getD 9 false = (if p = 0 then none else inpChain M w (t + 1) (p - 1)).isSome)
    (hcv : l.getD 10 false =
      (if p = 0 then none else inpChain M w (t + 1) (p - 1)).getD false) :
    cfgF M (some none) l = decide (((cfgAt M w (t + 1)).inputPos : ℕ) = p) ::
      optBits (inpChain M w (t + 1) p) := by
  have hstep := inp_step M (cfgAt M w t) hp
  have hsnap : snapshotAt M w t = ((cfgAt M w t).state, (cfgAt M w t).inputSymbol,
      (cfgAt M w t).workTapeSymbols) := rfl
  have hrun : cfgAt M w (t + 1) = M.tm.step (cfgAt M w t) :=
    MultiTapeTM.runFrom_succ_eq_step'
  simp only [cfgF, h0, hprev, hL, hR, hps, hpv, hl, hm, hr, hcs, hcv, Bool.false_eq_true,
    if_false, optOf_isSome_getD]
  rw [hsnap, ← hstep, ← hrun, inpChain_eq M w (t + 1) p]
  by_cases h : ((cfgAt M w (t + 1)).inputPos : ℕ) = p <;> simp [h]

/-- **The snapshot rule**: fed with the previous snapshot and accumulator and the final
running symbols, it returns the true snapshot block.

**Proof sketch.** At `t = 0` the snapshot is the initial state with the read symbols,
and the accumulator is empty.  At `t + 1` the state is `stepState` of the decoded
previous snapshot (`Complexity.snapshotAt_state_succ`), the read symbols are supplied,
and the accumulator gains the previous emission (`Complexity.tableauAccepted_succ`). -/
theorem cfgF_snap (w : List Bool) (t : ℕ) (l : List Bool)
    (h0 : l.getD 0 false = decide (t = 0))
    (hacc : t ≠ 0 → l.getD 1 false = tableauAccepted M w (t - 1))
    (hs : l.getD 2 false = (cfgAt M w t).inputSymbol.isSome)
    (hv : l.getD 3 false = (cfgAt M w t).inputSymbol.getD false)
    (hws : ∀ τ : Fin M.k, l.getD (4 + 2 * τ) false = ((cfgAt M w t).workTapeSymbols τ).isSome)
    (hwv : ∀ τ : Fin M.k,
      l.getD (5 + 2 * τ) false = ((cfgAt M w t).workTapeSymbols τ).getD false)
    (hprev : t ≠ 0 →
      snapDecode M ((l.drop (4 + 2 * M.k)).take (snapWidth M)) = snapshotAt M w (t - 1)) :
    cfgF M none l = snapExp M w t := by
  simp only [cfgF, snapExp, hs, hv, hws, hwv, optOf_isSome_getD, h0]
  cases t with
  | zero =>
    have ha : tableauAccepted M w 0 = false := by simp [tableauAccepted]
    simp only [decide_true, if_true, ha]
    rfl
  | succ t =>
    simp only [Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, if_false,
      hacc (Nat.succ_ne_zero t), hprev (Nat.succ_ne_zero t), Nat.add_sub_cancel]
    rw [tableauAccepted_succ]
    congr 2
    exact Prod.ext (snapshotAt_state_succ M w t).symm rfl

end Complexity
