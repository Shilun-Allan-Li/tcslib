/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.UnaryTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unary counter programs and their Turing machines

A small programming model for the polynomial-time *emitters* of [AB09, §6.2] (the machine
that prints the circuit of [AB09, Thm 6.6], Remark 6.7): a **counter program** is a goto
program over finitely many registers holding natural numbers, which can increment,
decrement and zero-test a register, print a bit or print the value of a register in unary,
and read its input once from left to right.  Every counter program is compiled into a
binary multi-tape Turing machine of the library's model (`Turing.FinTM`), one work tape
per register holding the value in unary, and an abstract run of `t` steps is simulated in
at most `t (2t + 3)` machine steps (`Complexity.CounterProg.exists_tm`).  Hence a string
function computed by a counter program in polynomially many abstract steps is
polynomial-time computable (`Complexity.CounterProg.polyTimeComputable`,
`TCSlib.Complexity.ClassNP.CounterProgPolyTime`).

The compilation follows the three-counter machine of the `CKT-SAT ≤p 3SAT` emitter
(`CircuitComplexity/CircuitSatReductionMachine.lean`), made generic: a register of value
`v` is the tape `1ᵛ` (`Turing.UnaryTape.ones`) with its head on the blank cell `v`.

Counter programs keep their registers in **unary**, which suits polynomial-time
emitters. The logarithmic-space counterpart, with registers in binary and a read-only
input, is the abstract register machine `Complexity.LogProg` of
`TCSlib.Complexity.SpaceComplexity.Machines` (cf. `SpaceComplexity/Machines/ARM.lean`);
a polynomially-running counter program is simulated by one in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Main definitions

* `Complexity.CounterProg.Instr`, `Complexity.CounterProg.St` — instructions and abstract
  states; `Complexity.CounterProg.step`, `Complexity.CounterProg.run` — the semantics.
* `Complexity.CounterProg.toTM` — the compiled machine.

## Main results

* `Complexity.CounterProg.sim_step` — one abstract step is at most `2B + 3` machine steps
  when all registers are at most `B`.
* (The simulation of whole runs, `Complexity.CounterProg.exists_tm`, is in
  `TCSlib.Complexity.TuringMachine.CounterProgRun`.)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§1.2: the multi-tape machine; §6.2, Remark 6.7.)
-/

namespace Complexity

namespace CounterProg

open Turing Turing.UnaryTape

/-! ## Programs and their semantics -/

/-- An instruction of a counter program over `R` registers with labels `Λ`: halt, jump,
print a bit, increment or decrement (saturating at `0`) a register, branch on a register
being zero, print a register's value in unary (`1ᵛ`), or read the next input symbol
(branching on end-of-input / `0` / `1`; a read symbol is consumed). -/
inductive Instr (R : ℕ) (Λ : Type) where
  /-- Stop. -/
  | halt
  /-- Jump to `next`. -/
  | goto (next : Λ)
  /-- Print the bit `b`. -/
  | out (b : Bool) (next : Λ)
  /-- Increment register `r`. -/
  | inc (r : Fin R) (next : Λ)
  /-- Decrement register `r` (`0` stays `0`). -/
  | dec (r : Fin R) (next : Λ)
  /-- Go to `zero` if register `r` is `0`, else to `pos`. -/
  | jz (r : Fin R) (zero pos : Λ)
  /-- Print `1ᵛ`, `v` the value of register `r`. -/
  | pr (r : Fin R) (next : Λ)
  /-- Read the next input symbol: at the end go to `onEnd`, else consume it and go to
  `onFalse` or `onTrue`. -/
  | rd (onEnd onFalse onTrue : Λ)

/-- An abstract state: the current label (`none` once halted), the registers, the number
of input symbols consumed, and the output so far. -/
@[ext]
structure St (R : ℕ) (Λ : Type) where
  /-- The current label, `none` when halted. -/
  lbl : Option Λ
  /-- The register values. -/
  regs : Fin R → ℕ
  /-- The number of input symbols read. -/
  pos : ℕ
  /-- The output printed so far. -/
  out : List Bool

variable {R : ℕ} {Λ : Type}

/-- **One step** of the program `P` on input `x`. -/
def step (P : Λ → Instr R Λ) (x : List Bool) (s : St R Λ) : St R Λ :=
  match s.lbl with
  | none => s
  | some l =>
    match P l with
    | .halt => ⟨none, s.regs, s.pos, s.out⟩
    | .goto l' => ⟨some l', s.regs, s.pos, s.out⟩
    | .out b l' => ⟨some l', s.regs, s.pos, s.out ++ [b]⟩
    | .inc r l' => ⟨some l', Function.update s.regs r (s.regs r + 1), s.pos, s.out⟩
    | .dec r l' => ⟨some l', Function.update s.regs r (s.regs r - 1), s.pos, s.out⟩
    | .jz r l0 l1 => ⟨some (if s.regs r = 0 then l0 else l1), s.regs, s.pos, s.out⟩
    | .pr r l' => ⟨some l', s.regs, s.pos, s.out ++ List.replicate (s.regs r) true⟩
    | .rd le lf lt =>
      match x[s.pos]? with
      | none => ⟨some le, s.regs, s.pos, s.out⟩
      | some false => ⟨some lf, s.regs, s.pos + 1, s.out⟩
      | some true => ⟨some lt, s.regs, s.pos + 1, s.out⟩

/-- `t` steps of the program. -/
def run (P : Λ → Instr R Λ) (x : List Bool) (s : St R Λ) (t : ℕ) : St R Λ :=
  (step P x)^[t] s

/-- The initial state at label `l₀`: all registers `0`, nothing read or printed. -/
def init (l₀ : Λ) : St R Λ := ⟨some l₀, fun _ => 0, 0, []⟩

variable (P : Λ → Instr R Λ) (x : List Bool)

/-- Zero steps change nothing. -/
theorem run_zero (s : St R Λ) : run P x s 0 = s := rfl

/-- Running `a + b` steps is running `a` steps, then `b`. -/
theorem run_add (s : St R Λ) (a b : ℕ) : run P x s (a + b) = run P x (run P x s a) b := by
  simp only [run, Nat.add_comm a b, Function.iterate_add_apply]

/-- Running `t + 1` steps is one step, then `t` steps. -/
theorem run_succ (s : St R Λ) (t : ℕ) : run P x s (t + 1) = run P x (step P x s) t := by
  simp only [run, Function.iterate_succ_apply]

/-- A halted state does not change. -/
theorem run_of_halted (s : St R Λ) (h : s.lbl = none) (t : ℕ) : run P x s t = s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, show step P x s = s by simp [step, h], ih]

/-- A step increases each register by at most one. -/
theorem step_regs_le (s : St R Λ) (r : Fin R) : (step P x s).regs r ≤ s.regs r + 1 := by
  unfold step
  split
  · omega
  · split <;> (try split) <;> simp only [Function.update_apply] <;> (try split_ifs) <;>
      first | omega | (subst_vars; omega)

/-- A step never moves past the end of the input. -/
theorem step_pos_le (s : St R Λ) (h : s.pos ≤ x.length) : (step P x s).pos ≤ x.length := by
  unfold step
  split
  · exact h
  · split <;> try exact h
    split
    · exact h
    all_goals
      rename_i heq
      have := (List.getElem?_eq_some_iff.mp heq).1
      simp only; omega

/-- After `t` steps each register has grown by at most `t`. -/
theorem run_regs_le (s : St R Λ) (r : Fin R) (t : ℕ) : (run P x s t).regs r ≤ s.regs r + t := by
  induction t generalizing s with
  | zero => simp [run_zero]
  | succ t ih =>
    rw [run_succ]
    have := ih (step P x s)
    have := step_regs_le P x s r
    omega

/-! ## The compiled machine -/

/-- The control states of the compiled machine: executing a label (`main`), or in the
middle of a decrement, a zero test, or the two walks of a print. -/
inductive TSt (R : ℕ) (Λ : Type) where
  /-- About to execute the instruction at label `l`. -/
  | main (l : Λ)
  /-- Second step of a decrement of `r`. -/
  | decB (r : Fin R) (l : Λ)
  /-- Second step of a zero test of `r`. -/
  | jzB (r : Fin R) (l0 l1 : Λ)
  /-- Printing register `r`: walking left over its cells. -/
  | prW (r : Fin R) (l : Λ)
  /-- Printing register `r`: walking back right. -/
  | prB (r : Fin R) (l : Λ)
  deriving DecidableEq, Fintype

/-- An action on work tape `t` only. -/
def act (t : Fin R) (im : SignType) (wr : Option (Option Bool)) (m : SignType)
    (o : Option Bool) (q : Option (TSt R Λ)) : Action R Bool (TSt R Λ) :=
  ⟨im, fun i => if i = t then (wr, m) else (none, 0), o, q⟩

/-- An action touching no work tape. -/
def ctl (im : SignType) (o : Option Bool) (q : Option (TSt R Λ)) : Action R Bool (TSt R Λ) :=
  ⟨im, fun _ => (none, 0), o, q⟩

/-- **The transition table** of the compiled machine. -/
def tr : TSt R Λ → Option Bool → (Fin R → Option Bool) → Action R Bool (TSt R Λ)
  | .main l, sym, _ =>
    match P l with
    | .halt => ctl 0 none none
    | .goto l' => ctl 0 none (some (.main l'))
    | .out b l' => ctl 0 (some b) (some (.main l'))
    | .inc r l' => act r 0 (some (some true)) .pos none (some (.main l'))
    | .dec r l' => act r 0 none .neg none (some (.decB r l'))
    | .jz r l0 l1 => act r 0 none .neg none (some (.jzB r l0 l1))
    | .pr r l' => act r 0 none .neg none (some (.prW r l'))
    | .rd le lf lt =>
      match sym with
      | none => ctl 0 none (some (.main le))
      | some false => ctl .pos none (some (.main lf))
      | some true => ctl .pos none (some (.main lt))
  | .decB r l, _, w =>
    if (w r).isSome then act r 0 (some none) 0 none (some (.main l))
    else act r 0 none .pos none (some (.main l))
  | .jzB r l0 l1, _, w =>
    if (w r).isSome then act r 0 none .pos none (some (.main l1))
    else act r 0 none .pos none (some (.main l0))
  | .prW r l, _, w =>
    if (w r).isSome then act r 0 none .neg (some true) (some (.prW r l))
    else act r 0 none .pos none (some (.prB r l))
  | .prB r l, _, w =>
    if (w r).isSome then act r 0 none .pos none (some (.prB r l))
    else ctl 0 none (some (.main l))

/-- **The machine of a counter program**: one work tape per register, started at `l₀`. -/
def toTM [Fintype Λ] [DecidableEq Λ] (l₀ : Λ) : FinTM Bool where
  k := R
  State := TSt R Λ
  tm := { q₀ := .main l₀, tr := tr P }

variable [Fintype Λ] [DecidableEq Λ] (l₀ : Λ)

/-- The machine configuration of an abstract state: register `r` of value `v` is the tape
`1ᵛ` with its head on cell `v`; the input head reads symbol `pos`. -/
def enc (s : St R Λ) : Cfg R Bool (TSt R Λ) x :=
  ⟨s.lbl.map .main, ⟨min (s.pos + 1) (x.length + 1), by omega⟩, fun r => ones (s.regs r),
    fun r => (s.regs r : ℤ), s.out⟩

/-- One machine step from a running configuration applies the transition. -/
theorem step_some (q : TSt R Λ) (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool)
    (hd : Fin R → ℤ) (out : List Bool) :
    (toTM P l₀).tm.step (⟨some q, p, tp, hd, out⟩ : Cfg R Bool (TSt R Λ) x) =
      (tr P q (Cfg.inputSymbol (⟨some q, p, tp, hd, out⟩ : Cfg R Bool (TSt R Λ) x))
        (fun i => tp i (hd i))).apply ⟨some q, p, tp, hd, out⟩ := rfl

omit [Fintype Λ] [DecidableEq Λ] in
/-- The effect of a one-tape action. -/
theorem apply_act {q' : Option (TSt R Λ)} (t : Fin R) (im : SignType)
    (wr : Option (Option Bool)) (m : SignType) (o : Option Bool) (q : Option (TSt R Λ))
    (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool) (hd : Fin R → ℤ)
    (out : List Bool) :
    (act t im wr m o q).apply (⟨q', p, tp, hd, out⟩ : Cfg R Bool (TSt R Λ) x) =
      ⟨q, moveInputPos p im, Function.update tp t (wrT (tp t) (hd t) wr),
        Function.update hd t (hd t + m), out ++ o.toList⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i = t
    · subst hi; cases wr <;> simp [act, Action.apply, wrT]
    · simp [act, Action.apply, hi]
  · funext i
    by_cases hi : i = t
    · subst hi; simp [act, Action.apply]
    · simp [act, Action.apply, hi]

omit [Fintype Λ] [DecidableEq Λ] in
/-- The effect of a tape-free action. -/
theorem apply_ctl {q' : Option (TSt R Λ)} (im : SignType) (o : Option Bool)
    (q : Option (TSt R Λ)) (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool)
    (hd : Fin R → ℤ) (out : List Bool) :
    (ctl im o q).apply (⟨q', p, tp, hd, out⟩ : Cfg R Bool (TSt R Λ) x) =
      ⟨q, moveInputPos p im, tp, hd, out ++ o.toList⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i; simp [ctl, Action.apply]
  · funext i; simp [ctl, Action.apply]

/-! ## The walks of a print -/

/-- The left walk of a print: in `prW r l`, from head `j - 1` over a register tape `1ᵐ`
(`j ≤ m`), the machine emits `j` ones in `j + 1` steps and turns into `prB r l` at head
`0`.

**Proof sketch.** Induction on `j`: at head `-1` the cell is blank and the head turns
right; at head `j - 1 ≥ 0` the cell holds `1`, which is emitted, and the head moves left. -/
theorem print_walk (r : Fin R) (l : Λ) (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool)
    (hd : Fin R → ℤ) (m : ℕ) (htp : tp r = ones m) :
    ∀ (j : ℕ) (out : List Bool), j ≤ m →
      (toTM P l₀).tm.runFrom (⟨some (.prW r l), p, tp, Function.update hd r ((j : ℤ) - 1),
        out⟩ : Cfg R Bool (TSt R Λ) x) (j + 1) =
        ⟨some (.prB r l), p, tp, Function.update hd r 0, out ++ List.replicate j true⟩ := by
  intro j
  induction j with
  | zero =>
    intro out _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    have hb : tp r (Function.update hd r ((0 : ℕ) - 1 : ℤ) r) = none := by
      simp [htp, ones_neg]
    simp only [tr, hb, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [apply_act]
    simp [wrT, moveInputPos_zero]
  | succ j ih =>
    intro out hj
    rw [MultiTapeTM.runFrom_succ_eq_step, step_some]
    have hb : tp r (Function.update hd r (((j + 1 : ℕ) : ℤ) - 1) r) = some true := by
      simp only [Function.update_self, htp]
      exact ones_lt (by omega) (by omega)
    simp only [tr, hb, Option.isSome_some, if_true]
    rw [apply_act]
    simp only [wrT, Function.update_eq_self, moveInputPos_zero, Function.update_idem,
      Function.update_self]
    rw [show (((j + 1 : ℕ) : ℤ) - 1 + ((SignType.neg : SignType) : ℤ)) = (j : ℤ) - 1 by
      simp [SignType.cast]; omega]
    rw [ih _ (by omega)]
    simp [List.replicate_succ', ← List.replicate_succ]

/-- The right walk of a print: in `prB r l`, from head `m - d` over `1ᵐ`, the machine walks
right to the blank cell `m` in `d + 1` steps and resumes at label `l`.

**Proof sketch.** Induction on `d`: at cell `m` the cell is blank and the machine resumes;
at cell `m - d - 1 < m` the cell holds `1` and the head moves right. -/
theorem back_walk (r : Fin R) (l : Λ) (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool)
    (hd : Fin R → ℤ) (m : ℕ) (htp : tp r = ones m) (out : List Bool) :
    ∀ d : ℕ, d ≤ m →
      (toTM P l₀).tm.runFrom (⟨some (.prB r l), p, tp,
        Function.update hd r (((m - d : ℕ) : ℤ)), out⟩ : Cfg R Bool (TSt R Λ) x) (d + 1) =
        ⟨some (.main l), p, tp, Function.update hd r (m : ℤ), out⟩ := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    have hb : tp r (Function.update hd r (((m - 0 : ℕ) : ℤ)) r) = none := by
      simp [htp, ones_ge]
    simp only [tr, hb, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [apply_ctl]
    simp [moveInputPos_zero]
  | succ d ih =>
    intro hd'
    rw [MultiTapeTM.runFrom_succ_eq_step, step_some]
    have hb : tp r (Function.update hd r (((m - (d + 1) : ℕ) : ℤ)) r) = some true := by
      simp only [Function.update_self, htp]
      exact ones_lt (by omega) (by omega)
    simp only [tr, hb, Option.isSome_some, if_true]
    rw [apply_act]
    simp only [wrT, Function.update_eq_self, moveInputPos_zero, Function.update_idem,
      Function.update_self, Option.toList_none, List.append_nil]
    rw [show (((m - (d + 1) : ℕ) : ℤ) + ((SignType.pos : SignType) : ℤ)) =
      (((m - d : ℕ) : ℤ)) by simp [SignType.cast]; omega]
    exact ih (by omega)

/-! ## Simulation of one step -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- Updating one register tape is the tape vector of the updated registers. -/
theorem tapes_update (ρ : Fin R → ℕ) (t : Fin R) (m : ℕ) :
    Function.update (fun r => ones (ρ r)) t (ones m) =
      fun r => ones (Function.update ρ t m r) := by
  funext i
  by_cases hi : i = t
  · subst hi; simp
  · simp [hi]

omit [Fintype Λ] [DecidableEq Λ] in
/-- Updating one head is the head vector of the updated registers. -/
theorem heads_update (ρ : Fin R → ℕ) (t : Fin R) (m : ℕ) :
    Function.update (fun r => ((ρ r : ℕ) : ℤ)) t (m : ℤ) =
      fun r => ((Function.update ρ t m r : ℕ) : ℤ) := by
  funext i
  by_cases hi : i = t
  · subst hi; simp
  · simp [hi]

omit [Fintype Λ] [DecidableEq Λ] in
/-- The input position of `enc` when the reading position is within the input. -/
theorem enc_inputPos (s : St R Λ) (h : s.pos ≤ x.length) :
    ((enc x s).inputPos : ℕ) = s.pos + 1 := by
  simp [enc]; omega

omit [Fintype Λ] [DecidableEq Λ] in
/-- The symbol read in `enc`. -/
theorem enc_inputSymbol (s : St R Λ) (h : s.pos ≤ x.length) :
    (enc x s).inputSymbol = x[s.pos]? :=
  FinTM.inputSymbol_at _ s.pos h (enc_inputPos x s h)

/-- **One abstract step is at most `2B + 3` machine steps**, when every register is at most
`B` and the reading position is within the input.

**Proof sketch.** Case analysis on the instruction.  Jumps, prints of a bit, increments and
reads are one machine step (an increment writes `1` on the blank cell under the head and
steps right); decrements and zero tests step left onto the last cell of the register and
then act on what they read (two steps); printing a register of value `v` steps left and
walks left over its `v` cells emitting `1`s and back right (`print_walk`, `back_walk`),
`2v + 3` steps. -/
theorem sim_step (s : St R Λ) (l : Λ) (hl : s.lbl = some l) (hp : s.pos ≤ x.length) (B : ℕ)
    (hB : ∀ r, s.regs r ≤ B) :
    ∃ t ≤ 2 * B + 3, (toTM P l₀).tm.runFrom (enc x s) t = enc x (step P x s) := by
  obtain ⟨lbl, ρ, pos, out⟩ := s
  simp only at hl hp hB
  subst hl
  have hsym := enc_inputSymbol x ⟨some l, ρ, pos, out⟩ hp
  set ip : Fin (x.length + 2) := ⟨min (pos + 1) (x.length + 1), by omega⟩ with hip
  have henc : enc x ⟨some l, ρ, pos, out⟩ =
      (⟨some (.main l), ip, fun r => ones (ρ r), fun r => (ρ r : ℤ), out⟩ :
        Cfg R Bool (TSt R Λ) x) := rfl
  have hone : ∀ c : Cfg R Bool (TSt R Λ) x, (toTM P l₀).tm.runFrom c 1 = (toTM P l₀).tm.step c :=
    fun c => rfl
  rw [henc] at hsym ⊢
  cases hP : P l with
  | halt =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some]
    simp only [tr, hP]
    rw [apply_ctl, moveInputPos_zero]
    simp [step, hP, enc, hip]
  | goto l' =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some]
    simp only [tr, hP]
    rw [apply_ctl, moveInputPos_zero]
    simp [step, hP, enc, hip]
  | out b l' =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some]
    simp only [tr, hP]
    rw [apply_ctl, moveInputPos_zero]
    simp [step, hP, enc, hip]
  | inc r l' =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some]
    simp only [tr, hP]
    rw [apply_act, moveInputPos_zero]
    simp only [step, hP, enc, Option.map_some, wrT, update_ones_succ, Option.toList_none,
      List.append_nil]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · exact tapes_update ρ r (ρ r + 1)
    · rw [show ((ρ r : ℕ) : ℤ) + ((SignType.pos : SignType) : ℤ) = ((ρ r + 1 : ℕ) : ℤ) by
        simp [SignType.cast]]
      exact heads_update ρ r (ρ r + 1)
  | dec r l' =>
    refine ⟨2, by omega, ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, MultiTapeTM.runFrom_add, hone (MultiTapeTM.runFrom _ 1),
      hone, step_some]
    simp only [tr, hP]
    rw [apply_act, moveInputPos_zero, step_some]
    simp only [tr, wrT, Function.update_self, Function.update_eq_self, Option.toList_none,
      List.append_nil]
    rcases Nat.eq_zero_or_pos (ρ r) with h0 | h0
    · have hb : ones (ρ r) ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = none :=
        ones_neg (by simp [SignType.cast]; omega)
      simp only [hb, Option.isSome_none, Bool.false_eq_true, if_false]
      rw [apply_act, moveInputPos_zero]
      simp only [step, hP, enc, Option.map_some, wrT, Function.update_eq_self,
        Function.update_idem, Function.update_self, Option.toList_none, List.append_nil]
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        by_cases hi : i = r
        · subst hi; simp [h0]
        · simp [hi]
      · funext i
        by_cases hi : i = r
        · subst hi; simp [h0, SignType.cast]
        · simp [hi]
    · obtain ⟨v, hv⟩ : ∃ v, ρ r = v + 1 := ⟨ρ r - 1, by omega⟩
      have hb : ones (ρ r) ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = some true :=
        ones_lt (by simp [SignType.cast]; omega) (by simp [SignType.cast])
      simp only [hb, Option.isSome_some, if_true]
      rw [apply_act, moveInputPos_zero]
      simp only [step, hP, enc, Option.map_some, wrT, Function.update_self,
        Function.update_idem, Option.toList_none, List.append_nil]
      have hz : ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = ((v : ℕ) : ℤ) := by
        simp [SignType.cast]; omega
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · rw [hz, hv, update_ones_pred, show v + 1 - 1 = v by omega]
        exact tapes_update ρ r v
      · rw [hz, hv, show v + 1 - 1 = v by omega,
          show ((v : ℕ) : ℤ) + ((0 : SignType) : ℤ) = ((v : ℕ) : ℤ) by simp]
        exact heads_update ρ r v
  | jz r l0 l1 =>
    refine ⟨2, by omega, ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, MultiTapeTM.runFrom_add, hone (MultiTapeTM.runFrom _ 1),
      hone, step_some]
    simp only [tr, hP]
    rw [apply_act, moveInputPos_zero, step_some]
    simp only [tr, wrT, Function.update_self, Function.update_eq_self, Option.toList_none,
      List.append_nil]
    have hback : ∀ (q : TSt R Λ), (act r 0 none .pos none (some q)).apply
        (⟨some (TSt.jzB r l0 l1), ip, fun r => ones (ρ r),
          Function.update (fun r => ((ρ r : ℕ) : ℤ)) r ((ρ r : ℤ) + ((SignType.neg : SignType) :
              ℤ)),
          out⟩ : Cfg R Bool (TSt R Λ) x) =
        ⟨some q, ip, fun r => ones (ρ r), fun r => (ρ r : ℤ), out⟩ := by
      intro q
      rw [apply_act, moveInputPos_zero]
      refine Cfg.ext rfl rfl ?_ ?_ (by simp)
      · simp [wrT]
      · funext i
        by_cases hi : i = r
        · subst hi; simp [SignType.cast]
        · simp [hi]
    rcases Nat.eq_zero_or_pos (ρ r) with h0 | h0
    · have hb : ones (ρ r) ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = none :=
        ones_neg (by simp [SignType.cast]; omega)
      simp only [hb, Option.isSome_none, Bool.false_eq_true, if_false]
      rw [hback]
      simp [step, hP, enc, h0, hip]
    · have hb : ones (ρ r) ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = some true :=
        ones_lt (by simp [SignType.cast]; omega) (by simp [SignType.cast])
      simp only [hb, Option.isSome_some, if_true]
      rw [hback]
      simp [step, hP, enc, show ρ r ≠ 0 by omega, hip]
  | pr r l' =>
    refine ⟨1 + (ρ r + 1) + (ρ r + 1), by have := hB r; omega, ?_⟩
    have h1 : (toTM P l₀).tm.runFrom (⟨some (.main l), ip, fun r => ones (ρ r),
        fun r => (ρ r : ℤ), out⟩ : Cfg R Bool (TSt R Λ) x) 1 =
        ⟨some (.prW r l'), ip, fun r => ones (ρ r),
          Function.update (fun r => ((ρ r : ℕ) : ℤ)) r (((ρ r : ℕ) : ℤ) - 1), out⟩ := by
      rw [hone, step_some]
      simp only [tr, hP]
      rw [apply_act, moveInputPos_zero]
      simp only [wrT, Function.update_eq_self, Option.toList_none, List.append_nil]
      rw [show ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = ((ρ r : ℕ) : ℤ) - 1 by
        simp [SignType.cast]; omega]
      rfl
    have h2 := print_walk P x l₀ r l' ip (fun r => ones (ρ r)) (fun r => (ρ r : ℤ)) (ρ r) rfl
      (ρ r) out le_rfl
    have h3 := back_walk P x l₀ r l' ip (fun r => ones (ρ r)) (fun r => (ρ r : ℤ)) (ρ r) rfl
      (out ++ List.replicate (ρ r) true) (ρ r) le_rfl
    rw [show (((ρ r - ρ r : ℕ) : ℤ)) = 0 by simp] at h3
    rw [MultiTapeTM.runFrom_add _ (1 + (ρ r + 1)) (ρ r + 1),
      MultiTapeTM.runFrom_add _ 1 (ρ r + 1), h1]
    erw [h2, h3]
    simp [step, hP, enc, hip]
  | rd le lf lt =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some, hsym]
    simp only [tr, hP]
    cases hx : x[pos]? with
    | none =>
      simp only
      rw [apply_ctl, moveInputPos_zero]
      simp [step, hP, hx, enc, hip]
    | some b =>
      have hlt : pos < x.length := (List.getElem?_eq_some_iff.mp hx).1
      have hmv : moveInputPos ip .pos =
          (⟨min (pos + 1 + 1) (x.length + 1), by omega⟩ : Fin (x.length + 2)) := by
        rw [moveInputPos_pos_of_ne_right _ (by simp [hip]; omega)]
        apply Fin.ext; simp [hip]; omega
      cases b <;> (simp only; rw [apply_ctl, hmv]; simp [step, hP, hx, enc])

end CounterProg

end Complexity
