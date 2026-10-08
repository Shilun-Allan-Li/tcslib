/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.TuringMachine.CounterProg

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reasoning about counter programs

Hoare-style run lemmas for the counter programs of `TCSlib.Complexity.TuringMachine.CounterProg`: the
relation `Complexity.CounterProg.Goes` ("from this label and these registers the program
reaches that label and those registers, printing `e`, within `b` steps"), its
composition, one lemma per instruction, the count-down loop, straight-line *templates*
(lists of print-a-bit / print-a-register micro-operations, the shape in which the emitter
of [AB09, Remark 6.7] prints a gadget of the circuit), and *linear expressions* — sums of
registers plus a constant, printed in unary by a template.

## Main definitions

* `Complexity.CounterProg.Goes` — the run relation.
* `Complexity.CounterProg.MOp`, `Complexity.CounterProg.tmplInstr` — template micro-operations
  and the instruction executing one.
* `Complexity.CounterProg.LinE` — linear expressions in the registers.

## Main results

* `Complexity.CounterProg.sim_run` — a run of `t` abstract steps is at most `t (2B + 3)`
  machine steps.
* `Complexity.CounterProg.exists_tm` — a halting abstract run of `t` steps is a machine
  computation within `t (2t + 3)` steps.
* `Complexity.CounterProg.Goes.trans` — composition.
* `Complexity.CounterProg.goes_loop` — the count-down loop.
* `Complexity.CounterProg.goes_tmpl` — running a template prints its micro-operations.
* `Complexity.CounterProg.flatMap_exec_linOps` — a linear expression prints its value in
  unary.
* `Complexity.CounterProg.run_pos_le`, `run_out`, `run_init_out_le` — the input position
  and the output grow boundedly along a run.

The consequence for polynomial time (`Complexity.CounterProg.polyTimeComputable`,
`polyTimeComputable_of_goes`) is in `TCSlib.Complexity.ClassNP.CounterProgPolyTime`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.2, Remark 6.7.)
-/

namespace Complexity

namespace CounterProg

variable {R : ℕ} {Λ : Type} (P : Λ → Instr R Λ) (x : List Bool)

/-! ## The run relation -/

/-- From label `l` with registers `ρ`, having read `p` input symbols, the program reaches the
label `l'` (`none`: it halts) with registers `ρ'` and `p'` symbols read, printing `e`, within
`b` steps (whatever was printed before). -/
def Goes (l : Λ) (ρ : Fin R → ℕ) (p : ℕ) (l' : Option Λ) (ρ' : Fin R → ℕ) (p' : ℕ)
    (e : List Bool) (b : ℕ) : Prop :=
  ∀ o, ∃ t ≤ b, run P x ⟨some l, ρ, p, o⟩ t = ⟨l', ρ', p', o ++ e⟩

variable {P x}

/-- Runs compose: bounds add and outputs concatenate. -/
theorem Goes.trans {l l' : Λ} {l'' : Option Λ} {ρ ρ' ρ'' : Fin R → ℕ} {p p' p'' : ℕ}
    {e e' : List Bool} {b b' : ℕ} (h : Goes P x l ρ p (some l') ρ' p' e b)
    (h' : Goes P x l' ρ' p' l'' ρ'' p'' e' b') : Goes P x l ρ p l'' ρ'' p'' (e ++ e') (b + b') := by
  intro o
  obtain ⟨t, ht, h1⟩ := h o
  obtain ⟨t', ht', h2⟩ := h' (o ++ e)
  exact ⟨t + t', by omega, by rw [run_add, h1, h2, List.append_assoc]⟩

/-- A bound can be weakened. -/
theorem Goes.mono {l : Λ} {l' : Option Λ} {ρ ρ' : Fin R → ℕ} {p p' : ℕ} {e : List Bool}
    {b b' : ℕ} (h : Goes P x l ρ p l' ρ' p' e b) (hb : b ≤ b') : Goes P x l ρ p l' ρ' p' e b' :=
  fun o => let ⟨t, ht, h1⟩ := h o; ⟨t, by omega, h1⟩

/-- The registers and position can be rewritten along equalities. -/
theorem Goes.congr {l : Λ} {l' : Option Λ} {ρ ρ' σ σ' : Fin R → ℕ} {p p' q q' : ℕ}
    {e e' : List Bool} {b b' : ℕ} (h : Goes P x l ρ p l' ρ' p' e b) (h1 : ρ = σ) (h2 : ρ' = σ')
    (h3 : p = q) (h4 : p' = q') (h5 : e = e') (h6 : b ≤ b') : Goes P x l σ q l' σ' q' e' b' := by
  subst h1 h2 h3 h4 h5; exact h.mono h6

/-- One step of a running state. -/
theorem goes_of_step {l : Λ} {ρ : Fin R → ℕ} {p : ℕ} {l' : Option Λ} {ρ' : Fin R → ℕ} {p' : ℕ}
    {e : List Bool} (h : ∀ o, step P x ⟨some l, ρ, p, o⟩ = ⟨l', ρ', p', o ++ e⟩) :
    Goes P x l ρ p l' ρ' p' e 1 :=
  fun o => ⟨1, le_rfl, h o⟩

/-! ## One instruction -/

section Instructions

variable {l l' : Λ} {ρ : Fin R → ℕ} {p : ℕ}

/-- A `halt` instruction stops the program in one step. -/
theorem goes_halt (h : P l = .halt) : Goes P x l ρ p none ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- A `goto` instruction jumps in one step. -/
theorem goes_goto (h : P l = .goto l') : Goes P x l ρ p (some l') ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- An `out b` instruction prints `b` in one step. -/
theorem goes_out {b : Bool} (h : P l = .out b l') : Goes P x l ρ p (some l') ρ p [b] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- An `inc r` instruction increments register `r` in one step. -/
theorem goes_inc {r : Fin R} (h : P l = .inc r l') :
    Goes P x l ρ p (some l') (Function.update ρ r (ρ r + 1)) p [] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- A `dec r` instruction decrements register `r` (saturating) in one step. -/
theorem goes_dec {r : Fin R} (h : P l = .dec r l') :
    Goes P x l ρ p (some l') (Function.update ρ r (ρ r - 1)) p [] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- A zero test on a register holding `0` takes the `zero` branch. -/
theorem goes_jz_zero {r : Fin R} {l0 l1 : Λ} (h : P l = .jz r l0 l1) (hr : ρ r = 0) :
    Goes P x l ρ p (some l0) ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h, hr]

/-- A zero test on a register not holding `0` takes the other branch. -/
theorem goes_jz_pos {r : Fin R} {l0 l1 : Λ} (h : P l = .jz r l0 l1) (hr : ρ r ≠ 0) :
    Goes P x l ρ p (some l1) ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h, hr]

/-- A `pr r` instruction prints the value of register `r` in unary in one step. -/
theorem goes_pr {r : Fin R} (h : P l = .pr r l') :
    Goes P x l ρ p (some l') ρ p (List.replicate (ρ r) true) 1 :=
  goes_of_step fun o => by simp [step, h]

/-- Reading at the end of the input takes the end branch, consuming nothing. -/
theorem goes_rd_end {le lf lt : Λ} (h : P l = .rd le lf lt) (hx : x[p]? = none) :
    Goes P x l ρ p (some le) ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h, hx]

/-- Reading a `0` takes the `0` branch and consumes it. -/
theorem goes_rd_false {le lf lt : Λ} (h : P l = .rd le lf lt) (hx : x[p]? = some false) :
    Goes P x l ρ p (some lf) ρ (p + 1) [] 1 :=
  goes_of_step fun o => by simp [step, h, hx]

/-- Reading a `1` takes the `1` branch and consumes it. -/
theorem goes_rd_true {le lf lt : Λ} (h : P l = .rd le lf lt) (hx : x[p]? = some true) :
    Goes P x l ρ p (some lt) ρ (p + 1) [] 1 :=
  goes_of_step fun o => by simp [step, h, hx]

end Instructions

/-! ## The count-down loop -/

/-- **The count-down loop.**  At `head` the program tests register `r` (exit when it is `0`),
otherwise decrements it and runs the body, which returns to `head`.  If iteration `j < K`
of the body takes the registers `st j` (with `r` already decremented to `K - j - 1`) to
`st (j + 1)` printing `em j`, and `st j r = K - j`, then the loop takes `st 0` to `st K`
printing `em 0 ++ … ++ em (K - 1)`.

**Proof sketch.** Induction on the number of remaining iterations. -/
theorem goes_loop {head dl body exit : Λ} {r : Fin R} (hh : P head = .jz r exit dl)
    (hd : P dl = .dec r body) (K : ℕ) (st : ℕ → Fin R → ℕ) (ps : ℕ → ℕ) (em : ℕ → List Bool)
    (b : ℕ) (hr : ∀ j ≤ K, st j r = K - j)
    (hbody : ∀ j < K, Goes P x body (Function.update (st j) r (K - j - 1)) (ps j) (some head)
      (st (j + 1)) (ps (j + 1)) (em j) b) :
    Goes P x head (st 0) (ps 0) (some exit) (st K) (ps K) ((List.range K).flatMap em)
      (K * (b + 2) + 1) := by
  have key : ∀ i ≤ K, Goes P x head (st (K - i)) (ps (K - i)) (some exit) (st K) (ps K)
      (((List.range i).map (fun j => K - i + j)).flatMap em) (i * (b + 2) + 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa using goes_jz_zero (ρ := st K) (p := ps K) hh (by simpa using hr K le_rfl)
    | succ i ih =>
      intro hi
      have h1 : st (K - (i + 1)) r ≠ 0 := by rw [hr _ (by omega)]; omega
      have hj : K - (i + 1) + 1 = K - i := by omega
      have hb := hbody (K - (i + 1)) (by omega)
      rw [hj, show K - (K - (i + 1)) - 1 = i by omega] at hb
      have hdec : Function.update (st (K - (i + 1))) r (st (K - (i + 1)) r - 1) =
          Function.update (st (K - (i + 1))) r i := by
        rw [hr _ (by omega)]; congr 1; omega
      have := (((goes_jz_pos (p := ps (K - (i + 1))) hh h1).trans
        (goes_dec (p := ps (K - (i + 1))) hd)).trans
          (hdec ▸ hb)).trans (ih (by omega))
      refine this.congr rfl rfl rfl rfl ?_ (by nlinarith)
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatMap_cons]
      simp only [List.nil_append, Nat.add_zero]
      congr 2
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]; omega
  simpa using key K le_rfl

/-! ## Templates -/

/-- A template micro-operation: print a bit, or print a register in unary. -/
inductive MOp (R : ℕ) where
  /-- Print the bit `b`. -/
  | out (b : Bool)
  /-- Print register `r` in unary. -/
  | pr (r : Fin R)

/-- What a micro-operation prints, with registers `ρ`. -/
def MOp.exec (ρ : Fin R → ℕ) : MOp R → List Bool
  | .out b => [b]
  | .pr r => List.replicate (ρ r) true

/-- The instruction at position `i` of a template run at labels `lab 0, lab 1, …`, continuing
at `next` after the last micro-operation. -/
def tmplInstr (tm : List (MOp R)) (lab : ℕ → Λ) (next : Λ) (i : ℕ) : Instr R Λ :=
  match tm[i]? with
  | some (.out b) => .out b (lab (i + 1))
  | some (.pr r) => .pr r (lab (i + 1))
  | none => .goto next

/-- **Running a template**: if the labels `lab i` hold the template's instructions, the
program prints the micro-operations' outputs in `|tm| + 1` steps and continues at `next`,
registers unchanged.

**Proof sketch.** Induction on the number of remaining micro-operations: each is one
`out` or `pr` step to the next label, and past the end a `goto` reaches `next`. -/
theorem goes_tmpl (tm : List (MOp R)) (lab : ℕ → Λ) (next : Λ)
    (hP : ∀ i ≤ tm.length, P (lab i) = tmplInstr tm lab next i) (ρ : Fin R → ℕ) (p : ℕ) :
    Goes P x (lab 0) ρ p (some next) ρ p (tm.flatMap (MOp.exec ρ)) (tm.length + 1) := by
  have key : ∀ d i, i + d = tm.length →
      Goes P x (lab i) ρ p (some next) ρ p ((tm.drop i).flatMap (MOp.exec ρ)) (d + 1) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h := hP i (by omega)
      rw [tmplInstr, List.getElem?_eq_none (by omega)] at h
      simpa [List.drop_eq_nil_of_le (show tm.length ≤ i by omega)] using goes_goto (ρ := ρ) (p :=
          p) h
    | succ d ih =>
      intro i hi
      have hlt : i < tm.length := by omega
      have h := hP i (by omega)
      rw [tmplInstr, List.getElem?_eq_getElem hlt] at h
      rw [List.drop_eq_getElem_cons hlt, List.flatMap_cons]
      have hrest := ih (i + 1) (by omega)
      cases hop : tm[i] with
      | out b =>
        rw [hop] at h
        exact ((goes_out h).trans hrest).mono (by omega)
      | pr r =>
        rw [hop] at h
        exact ((goes_pr h).trans hrest).mono (by omega)
  simpa using key tm.length 0 (by omega)

/-! ## Linear expressions -/

/-- A linear expression in the registers: a list of registers (with multiplicity) and a
constant; its value is the sum of the listed registers plus the constant. -/
abbrev LinE (R : ℕ) := List (Fin R) × ℕ

/-- The value of a linear expression. -/
def LinE.val (ρ : Fin R → ℕ) (e : LinE R) : ℕ := (e.1.map ρ).sum + e.2

/-- The micro-operations printing a linear expression in unary. -/
def linOps (e : LinE R) : List (MOp R) := e.1.map .pr ++ List.replicate e.2 (.out true)

/-- **A linear expression prints its value in unary.** -/
theorem flatMap_exec_linOps (ρ : Fin R → ℕ) (e : LinE R) :
    (linOps e).flatMap (MOp.exec ρ) = List.replicate (e.val ρ) true := by
  obtain ⟨rs, c⟩ := e
  simp only [linOps, LinE.val, List.flatMap_append]
  have h1 : (rs.map MOp.pr).flatMap (MOp.exec ρ) = List.replicate (rs.map ρ).sum true := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.map_cons, List.flatMap_cons, ih, List.sum_cons, MOp.exec,
        List.replicate_add]
  have h2 : (List.replicate c (MOp.out true : MOp R)).flatMap (MOp.exec ρ) =
      List.replicate c true := by
    induction c with
    | zero => rfl
    | succ c ih =>
      simp only [List.replicate_succ, List.flatMap_cons, ih, MOp.exec, List.singleton_append]
  rw [h1, h2, List.replicate_add]

/-- The micro-operations printing a fixed bit string. -/
def bitsOps (l : List Bool) : List (MOp R) := l.map .out

/-- A fixed bit string prints itself. -/
theorem flatMap_exec_bitsOps (ρ : Fin R → ℕ) (l : List Bool) :
    (bitsOps l : List (MOp R)).flatMap (MOp.exec ρ) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [bitsOps, List.map_cons, List.flatMap_cons,
      MOp.exec] at ih ⊢; rw [ih]; rfl

section SimRun

open Turing Turing.UnaryTape

variable (P : Λ → Instr R Λ) (x : List Bool) [Fintype Λ] [DecidableEq Λ] (l₀ : Λ)

/-! ## Simulation of a run -/

/-- **A run of `t` abstract steps is at most `t (2B + 3)` machine steps** when every
register starts at least `t` below `B` — growth by at most one per step then keeps every
intermediate valuation within `B`. (A bound on the intermediate valuations alone does not
satisfy this hypothesis; that broader interface is
`Complexity.CounterProg.sim_run_of_regs_le` below — P0 round 1, findings 2/S9.)

**Proof sketch.** Induction on `t`: a halted state is a halted configuration; otherwise
simulate one step (`sim_step`) and continue, registers having grown by at most one. -/
theorem sim_run (B : ℕ) : ∀ (t : ℕ) (s : St R Λ), s.pos ≤ x.length → (∀ r, s.regs r + t ≤ B) →
    ∃ t' ≤ t * (2 * B + 3), (toTM P l₀).tm.runFrom (enc x s) t' = enc x (run P x s t) := by
  intro t
  induction t with
  | zero => intro s _ _; exact ⟨0, by simp, rfl⟩
  | succ t ih =>
    intro s hp hB
    cases hl : s.lbl with
    | none => exact ⟨0, by omega, by rw [run_of_halted P x s hl]; rfl⟩
    | some l =>
      obtain ⟨t₁, ht₁, h₁⟩ := sim_step P x l₀ s l hl hp B (fun r => by have := hB r; omega)
      obtain ⟨t₂, ht₂, h₂⟩ := ih (step P x s) (step_pos_le P x s hp)
        (fun r => by have := hB r; have := step_regs_le P x s r; omega)
      refine ⟨t₁ + t₂, by nlinarith, ?_⟩
      rw [MultiTapeTM.runFrom_add, h₁, h₂, run_succ]

/-- **The reachable-bound run interface** (P0 round 1, sanity target S9): the simulation
bound of `Complexity.CounterProg.sim_run`, under a bound on every register valuation
actually reached strictly before the end of the run — rather than the start-`t`-below-`B`
headroom — at the per-step cost `2B + 5` (each pre-step valuation is at most `B`, so a
mid-step increment stays within `B + 1` and `Complexity.CounterProg.sim_step` at `B + 1`
costs at most `2(B + 1) + 3`).

**Proof sketch.** Induction on `t` exactly as in `Complexity.CounterProg.sim_run`, except
that each step's register bound comes from the reachability hypothesis at that step
(instantiated at `j`, then `Turing.CounterProg`-style `step_regs_le` gives the mid-step
`B + 1`) instead of the decreasing headroom; `step_pos_le` preserves the position bound. -/
theorem sim_run_of_regs_le (B : ℕ) (t : ℕ) (s : St R Λ) (hp : s.pos ≤ x.length)
    (hB : ∀ j < t, ∀ r, (run P x s j).regs r ≤ B) :
    ∃ t' ≤ t * (2 * B + 5), (toTM P l₀).tm.runFrom (enc x s) t' = enc x (run P x s t) := by
  sorry

/-- **A counter program is a Turing machine**: if the program halts on `x` after `t`
abstract steps, its machine computes the program's output within `t (2t + 3)` steps.

**Proof sketch.** The machine's initial configuration encodes the initial abstract state
(blank tapes are the registers `0`); registers stay below `t` during the run
(`run_regs_le`), so `sim_run` with `B = t` applies, and the halted configuration is
absorbing. -/
theorem exists_tm (x : List Bool) (t : ℕ) (h : (run P x (init l₀) t).lbl = none) :
    (toTM P l₀).ComputesInTime x (run P x (init l₀) t).out (t * (2 * t + 3)) := by
  have hinit : (toTM P l₀).tm.initCfg x = enc x (init l₀ : St R Λ) := by
    simp only [MultiTapeTM.initCfg, Cfg.init, enc, init]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext; simp
    · funext r; simp [ones_zero]
    · funext r; simp
  obtain ⟨t', ht', h'⟩ := sim_run P x l₀ t t (init l₀) (by simp [init])
    (fun r => by simp [init])
  have hhalt : ((toTM P l₀).tm.runFrom ((toTM P l₀).tm.initCfg x) t').state = none := by
    rw [hinit, h']; simp [enc, h]
  refine (FinTM.computesInTime_iff _ _ _ _).mpr ⟨?_, ?_⟩
  · have := (toTM P l₀).tm.runFrom_add ((toTM P l₀).tm.initCfg x) t' (t * (2 * t + 3) - t')
    rw [Nat.add_sub_of_le ht', MultiTapeTM.runFrom_of_halt _ hhalt] at this
    rw [this]; exact hhalt
  · have := (toTM P l₀).tm.runFrom_add ((toTM P l₀).tm.initCfg x) t' (t * (2 * t + 3) - t')
    rw [Nat.add_sub_of_le ht', MultiTapeTM.runFrom_of_halt _ hhalt] at this
    rw [this, hinit, h']; rfl

end SimRun

/-! ## Growth of positions and outputs -/

section Growth

variable (P x)

/-- The input position grows by at most one per step. -/
theorem run_pos_le (s : St R Λ) (t : ℕ) : (run P x s t).pos ≤ s.pos + t := by
  induction t generalizing s with
  | zero => simp [run_zero]
  | succ t ih =>
    rw [run_succ]
    have := ih (step P x s)
    have : (step P x s).pos ≤ s.pos + 1 := by
      unfold step; split
      · omega
      · split <;> (try split) <;> simp
    omega

/-- A step appends to the output. -/
theorem step_out (s : St R Λ) : ∃ e, (step P x s).out = s.out ++ e := by
  unfold step; split
  · exact ⟨[], by simp⟩
  · split <;> (try split) <;> simp

/-- A run appends to the output. -/
theorem run_out (s : St R Λ) (t : ℕ) : ∃ e, (run P x s t).out = s.out ++ e := by
  induction t generalizing s with
  | zero => exact ⟨[], by simp [run_zero]⟩
  | succ t ih =>
    rw [run_succ]
    obtain ⟨e, he⟩ := step_out P x s
    obtain ⟨e', he'⟩ := ih (step P x s)
    exact ⟨e ++ e', by rw [he', he, List.append_assoc]⟩

/-- A step prints at most one more than the largest register. -/
theorem step_out_le (s : St R Λ) (K : ℕ) (h : ∀ r, s.regs r ≤ K) :
    (step P x s).out.length ≤ s.out.length + K + 1 := by
  unfold step; split
  · omega
  · split <;> (try split) <;> simp <;> (try have := h ‹_›) <;> omega

/-- From the start, `t` steps print at most `t (t + 1)` bits. -/
theorem run_init_out_le (l₀ : Λ) (t : ℕ) : (run P x (init l₀) t).out.length ≤ t * (t + 1) := by
  induction t with
  | zero => simp [run_zero, init]
  | succ t ih =>
    rw [run_add, show run P x (run P x (init l₀) t) 1 = step P x (run P x (init l₀) t) from rfl]
    have := step_out_le P x (run P x (init l₀) t) t (fun r => by
      have := run_regs_le P x (init l₀) r t; simpa [init] using this)
    nlinarith

end Growth

end CounterProg

end Complexity
