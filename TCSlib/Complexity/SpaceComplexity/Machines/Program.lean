/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import TCSlib.Complexity.SpaceComplexity.Machines.Layout

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Register-tape programs with subroutine calls, and their compiled machines

A *register-tape program* (`Complexity.LogProg.RProg`) is a multi-tape machine over `m`
work tapes (its *registers*) in which some states are *call nodes*: in a call node the
program asks a fixed decider whether a *virtual input* — a part of its own input followed by
the words on some of its registers, `Complexity.LogProg.vword` — belongs to the decider's
language, and continues in one of two states. This is the "pretend there is a virtual input
tape" device of [AB09, proof of Lemma 4.17, Fig. 4.3], packaged once.

This file defines the program model and the machine `Complexity.LogProg.compileTM` that
realizes it: the registers become work tapes `0, …, m - 1`, the decider's work tapes follow,
and a call node is executed by simulating the decider step for step on the virtual input.
The virtual input head is represented by the real input head and the register heads
(`Complexity.LogProg.TPos`), so the simulation needs no extra space.

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Main definitions

* `Complexity.LogProg.Mode` — which part of the real input opens the virtual input: all of
  it, doubled (`whole`, giving `Turing.pairEncode x _`), or its leading run of `1`s, plain
  (`unaryFst`, giving `Turing.pairEncode 1ⁿ _` on inputs `Turing.pairEncode 1ⁿ _`).
* `Complexity.LogProg.CallSpec`, `Complexity.LogProg.RProg` — call nodes and programs.
* `Complexity.LogProg.callSegs` — the segments of the virtual input of a call.
* `Complexity.LogProg.CSt`, `Complexity.LogProg.ctr`, `Complexity.LogProg.compileTM` — the
  compiled machine.
* `Complexity.LogProg.seam` — the compiled configuration of a program configuration.

## Main results

* `Complexity.LogProg.step_seam_prog` — away from call nodes the compiled machine runs the
  program in lockstep.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

/-- Which part of the real input opens a virtual input. -/
inductive Mode where
  /-- the whole input, doubled: virtual inputs `pairEncode x _` -/
  | whole
  /-- the leading run of `1`s of the input, plain: on an input `pairEncode 1ⁿ _` this is
  `1²ⁿ`, so the virtual inputs are `pairEncode 1ⁿ _` -/
  | unaryFst
  deriving DecidableEq

/-- The first segment of a virtual input. -/
def Mode.seg0 : Mode → List Bool → Seg
  | .whole, x => (x, true)
  | .unaryFst, x => (x.takeWhile (· = true), false)

/-- The register segments: every word but the last is doubled. -/
def argSegs : List (List Bool) → List Seg
  | [] => []
  | [w] => [(w, false)]
  | w :: v :: ws => (w, true) :: argSegs (v :: ws)

/-- There is one register segment per argument word. -/
@[simp] lemma length_argSegs (ws : List (List Bool)) : (argSegs ws).length = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => cases ws with
    | nil => rfl
    | cons v ws => simp [argSegs] at ih ⊢; omega

/-- Segment `i` of the register segments is register word `i`, doubled unless last. -/
lemma seg_argSegs (ws : List (List Bool)) (i : ℕ) (hi : i < ws.length) :
    seg (argSegs ws) i = (ws[i], decide (i + 1 < ws.length)) := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases ws with
    | nil =>
      have : i = 0 := by simp at hi; omega
      subst this; simp [argSegs, seg]
    | cons v ws =>
      cases i with
      | zero => simp [argSegs, seg]
      | succ i =>
        simp only [argSegs, seg_cons_succ]
        rw [ih i (by simp at hi ⊢; omega)]
        simp

/-- A call node: the decider to call, the virtual-input mode, the argument registers, and
the two continuation states. -/
structure CallSpec (m d : ℕ) (Λ : Type) where
  /-- which decider -/
  dec : Fin d
  /-- the first segment of the virtual input -/
  mode : Mode
  /-- the registers whose words follow, in order -/
  args : List (Fin m)
  /-- the state after a positive answer -/
  yes : Λ
  /-- the state after a negative answer -/
  no : Λ

/-- A register-tape program over `m` registers calling `d` deciders: a machine on the
registers together with the set of call nodes (on which its transition table is ignored). -/
structure RProg (m d : ℕ) (Λ : Type) where
  /-- the transitions at the ordinary nodes -/
  tm : MultiTapeTM m Bool Λ
  /-- the call nodes -/
  call : Λ → Option (CallSpec m d Λ)

/-- The segments of the virtual input of a call on input `x` with register words `W`. -/
def callSegs {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (x : List Bool)
    (W : Fin m → List Bool) : List Seg :=
  cs.mode.seg0 x :: argSegs (cs.args.map W)

/-- A call's virtual input has one segment per argument register plus the leading segment. -/
@[simp] lemma length_callSegs {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (x : List Bool)
    (W : Fin m → List Bool) : (callSegs cs x W).length = cs.args.length + 1 := by
  simp [callSegs]

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
/-- The states of the compiled machine. -/
inductive CSt (Λ SD : Type) (m : ℕ) where
  /-- running the program at node `l` -/
  | prog (l : Λ)
  /-- simulating the decider (state `q`) for the call at `l`: current segment `s`, parity,
  direction of the last track move, and the decider's emitted bit so far -/
  | sim (l : Λ) (q : SD) (s : Fin (m + 1)) (par dir : Bool) (res : Option Bool)
  /-- returning: the mandatory first left move of the input rewind -/
  | ret1 (l : Λ) (s : Fin (m + 1)) (dir res : Bool)
  /-- returning: scanning the input head left -/
  | ret2 (l : Λ) (s : Fin (m + 1)) (dir res : Bool)
  /-- returning: restoring the head of argument register number `a` (`scan`: in its left
  scan) -/
  | retR (l : Λ) (s : Fin (m + 1)) (dir res : Bool) (a : Fin m) (scan : Bool)
  deriving DecidableEq, Fintype

/-- Track bookkeeping of one simulated step (a pure function): from the segment `s`, parity,
direction of the last move, whether the current track reads a cell, and the virtual head
move, compute the new segment, parity, direction, and the move of the current track's real
head. `dbl`: the segment is doubled; `last`/`first`: it is the last/first segment. -/
def gstep (dbl last first : Bool) (s : ℕ) (par dir isChar : Bool) :
    SignType → ℕ × Bool × Bool × SignType
  | .zero => (s, par, dir, 0)
  | .pos =>
    if isChar then (if dbl ∧ par = false then (s, true, dir, 0) else (s, false, true, .pos))
    else if dir then (if last then (s, par, dir, 0) else (s + 1, true, false, 0))
    else (s, false, true, .pos)
  | .neg =>
    if isChar then (if dbl ∧ par = true then (s, false, dir, 0) else (s, true, false, .neg))
    else if dir then (s, true, false, .neg)
    else (if first then (s, par, dir, 0) else (s - 1, false, true, 0))

/-- Clamp a natural number into `Fin (m + 1)`. -/
def toFin (m s : ℕ) : Fin (m + 1) := ⟨min s m, by omega⟩

/-- The rendering flag of segment `s` of a call (from the mode for `s = 0`). -/
def segDbl {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (s : ℕ) : Bool :=
  if s = 0 then decide (cs.mode = .whole) else decide (s < cs.args.length)

/-- The register read by segment `s ≥ 1` (a default otherwise). -/
def segReg {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (s : ℕ) (h : 0 < m) : Fin m :=
  cs.args.getD (s - 1) ⟨0, h⟩

/-- Whether segment `s`'s current reading is a cell of its word: a bit on a register or
on the input in `whole` mode, a `1` in `unaryFst` mode. -/
def isCharRead (mode : Mode) (s : ℕ) (rd : Option Bool) : Bool :=
  if s = 0 ∧ mode = .unaryFst then decide (rd = some true) else rd.isSome

/-- The virtual symbol presented to the decider. -/
def virtSym (mode : Mode) (s nseg : ℕ) (dir : Bool) (rd : Option Bool) : Option Bool :=
  if isCharRead mode s rd then (if s = 0 ∧ mode = .unaryFst then some true else rd)
  else if dir then (if s + 1 = nseg then none else some false)
  else (if s = 0 then none else some true)

/-- The register action of a return step on argument register `r`: move `mv`. -/
def regMove {m : ℕ} (r : Fin m) (mv : SignType) : Fin m → Option (Option Bool) × SignType :=
  fun r' => (none, if r' = r then mv else 0)

/-- The state after finishing argument register `a` of a return: the next argument register,
or back to the program. -/
def nextRet {Λ SD : Type} {m d : ℕ} (cs : CallSpec m d Λ) (l : Λ) (s : Fin (m + 1))
    (dir res : Bool) (a : ℕ) : CSt Λ SD m :=
  if h : a < cs.args.length ∧ a < m then .retR l s dir res ⟨a, h.2⟩ false
  else .prog (if res then cs.yes else cs.no)

section Compile

variable {m d kD : ℕ} {Λ SD : Type}

/-- The idle action on the decider block. -/
def dIdle : Fin kD → Option (Option Bool) × SignType := fun _ => (none, 0)

/-- **The transition table of the compiled machine.** See the module docstring; at a call
node the setup step moves the argument heads one cell left (onto the left blanks of their
words) and starts the decider; a simulated step reads the virtual symbol from the current
track, performs the decider's work-tape actions on the decider block, moves the current
track's real head according to `gstep`, and records the decider's emission; when the decider
halts the return phase rewinds the input head and the argument heads. -/
def ctr (P : RProg m d Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    CSt Λ SD m → Option Bool → (Fin (m + kD) → Option Bool) → Action (m + kD) Bool (CSt Λ SD m)
  | .prog l, inp, w =>
    match P.call l with
    | none =>
      let a := P.tm.tr l inp (fun r => w (Fin.castAdd kD r))
      ⟨a.inputTape, Fin.append a.workTapes dIdle, a.output, a.state.map .prog⟩
    | some cs =>
      ⟨0, Fin.append (fun r => (none, if r ∈ cs.args then -1 else 0)) dIdle, none,
        some (.sim l (q0 cs.dec) 0 false true none)⟩
  | .sim l q s par dir res, inp, w =>
    match P.call l with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some cs =>
      let rd : Option Bool :=
        if s.val = 0 then inp
        else if hm : 0 < m then w (Fin.castAdd kD (segReg cs s hm)) else none
      let ic := isCharRead cs.mode s rd
      let vs := virtSym cs.mode s (cs.args.length + 1) dir rd
      let a := D.tr q vs (fun i => w (Fin.natAdd m i))
      let g := gstep (segDbl cs s) (decide (s.val + 1 = cs.args.length + 1))
        (decide (s.val = 0)) s par dir ic a.inputTape
      let res' := res <|> a.output
      ⟨if s.val = 0 then g.2.2.2 else 0,
        Fin.append (fun r => (none, if h : 0 < m then
            (if s.val ≠ 0 ∧ r = segReg cs s h then g.2.2.2 else 0) else 0)) a.workTapes,
        none,
        some (match a.state with
          | some q' => .sim l q' (toFin m g.1) g.2.1 g.2.2.1 res'
          | none => .ret1 l (toFin m g.1) g.2.2.1 (res'.getD false))⟩
  | .ret1 l s dir res, _, _ => ⟨-1, fun _ => (none, 0), none, some (.ret2 l s dir res)⟩
  | .ret2 l s dir res, inp, _ =>
    match inp with
    | some _ => ⟨-1, fun _ => (none, 0), none, some (.ret2 l s dir res)⟩
    | none =>
      match P.call l with
      | none => ⟨0, fun _ => (none, 0), none, none⟩
      | some cs => ⟨1, fun _ => (none, 0), none, some (nextRet cs l s dir res 0)⟩
  | .retR l s dir res a scan, _, w =>
    match P.call l with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some cs =>
      let r := cs.args.getD a a
      let rd := w (Fin.castAdd kD r)
      let leftSide : Bool := decide (s.val < a.val + 1) || (decide (s.val = a.val + 1) && !dir)
      if scan then
        match rd with
        | some _ => ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩
        | none => ⟨0, Fin.append (regMove r 1) dIdle, none,
            some (nextRet cs l s dir res (a.val + 1))⟩
      else
        match rd with
        | none =>
          if leftSide then
            ⟨0, Fin.append (regMove r 1) dIdle, none, some (nextRet cs l s dir res (a.val + 1))⟩
          else ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩
        | some _ => ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩

/-- **The compiled machine** of a program `P` with start node `l₀`, calling the deciders
`D` from the start states `q0 j`. -/
def compileTM (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    MultiTapeTM (m + kD) Bool (CSt Λ SD m) where
  q₀ := .prog l₀
  tr := ctr P D q0

/-- The compiled configuration of a program configuration: the program's registers, the
decider block blank with heads at the origin. -/
def seam {x : List Bool} (c : Cfg m Bool Λ x) : Cfg (m + kD) Bool (CSt Λ SD m) x :=
  ⟨c.state.map .prog, c.inputPos, Fin.append c.workTapes (fun _ _ => none),
    Fin.append c.workTapePos (fun _ => 0), c.output⟩

/-- The initial configuration of the compiled machine is the seam of the program's. -/
lemma seam_init (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (x : List Bool) :
    (compileTM P l₀ D q0).initCfg x = seam (kD := kD) (Cfg.init (k := m) l₀ x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [seam, Cfg.init]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [seam, Cfg.init]

/-- **Lockstep away from calls**: at a non-call node the compiled machine makes exactly the
program's step.

**Proof sketch.** At a non-call program node the compiled transition is the program's
transition, relabelled (`ctr` on `prog` states), with the decider tapes untouched. Unfold one
step on both sides and compare the components of `seam`. -/
lemma step_seam_prog (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) {x : List Bool} (c : Cfg m Bool Λ x) (l : Λ) (hl : c.state = some l)
    (hcall : P.call l = none) :
    (compileTM P l₀ D q0).step (seam c) = seam (P.tm.step c) := by
  have hstate : (seam (kD := kD) (SD := SD) c).state = some (.prog l) := by
    simp [seam, hl]
  unfold MultiTapeTM.step
  rw [hstate, hl]
  have hin : (seam (kD := kD) (SD := SD) c).inputSymbol = c.inputSymbol := rfl
  have hw : (fun r => (seam (kD := kD) (SD := SD) c).workTapeSymbols (Fin.castAdd kD r)) =
      c.workTapeSymbols := by
    funext r; simp [seam, Cfg.workTapeSymbols]
  simp only [compileTM, ctr, hcall, hin, hw]
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [seam]
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i
    · simp only [Action.apply, Fin.append_left, seam]
    · simp [Action.apply, seam, dIdle]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i
    · simp [Action.apply, seam]
    · simp [Action.apply, seam, dIdle]

/-- A halted program configuration is a halted compiled configuration. -/
lemma seam_state_none {x : List Bool} (c : Cfg m Bool Λ x) (h : c.state = none) :
    (seam (kD := kD) (SD := SD) c).state = none := by
  simp [seam, h]

end Compile

end Complexity.LogProg
