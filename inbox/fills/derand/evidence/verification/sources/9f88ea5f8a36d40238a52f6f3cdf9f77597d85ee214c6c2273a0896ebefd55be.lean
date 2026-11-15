/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.SpaceComplexity.Machines.NARMKit
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic walk machine for `PATH`

[AB09, §4.1.2]: the machine `Complexity.LogProg.pathA`, a nondeterministic abstract register
machine with nine registers and the two input-access deciders
(`Complexity.inputBitLang`, `Complexity.inputLenLang`): it checks the unary prefix and the
matrix shape, guesses `s` and `t` and checks them against the input, then walks from `s`,
guessing each next vertex and reading its matrix bit, for at most `n` steps. This file
defines the machine and its register file and proves the walk loop correct
(`Complexity.LogProg.ps_walk`) in the continuation semantics of
`TCSlib.Complexity.SpaceComplexity.Machines.NARMKit`; the input checks and the assembly are in
`TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof`.

## Main definitions

* `Complexity.LogProg.PathLabel`, `Complexity.LogProg.pathA` — the machine.
* `Complexity.LogProg.pathAs`, `Complexity.LogProg.pathOr` — its deciders.
* `Complexity.LogProg.PReg` — its register file, by name; `Complexity.LogProg.PS` — the
  semantics at a label and register file.

## Main results

* `Complexity.LogProg.pathA_npreS` — the machine meets the syntactic preconditions.
* `Complexity.LogProg.ps_index` — the matrix position of an edge.
* `Complexity.LogProg.ps_walk` — the walk loop. [AB09, §4.1.2]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2.)
-/

namespace Complexity.LogProg

open Turing

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The labels of the walk machine: the unary scan (`u*`), the matrix scan (`m*`), the guess
and check of the source (`s*`) and of the target (`t*`), the walk (`w*`), the three
add-twice loops of the index computation (`ak k`, `ak₁ k`, `ak₂ k`, `ak₃ k`), and the two
answers. -/
inductive PathLabel
  | u0 | u1 | u2 | u3 | u4 | u5 | u6 | u7
  | m0 | mr | m1 | m2 | m3 | m4 | m5 | m7 | m8 | m9 | m10 | m11 | ms | m12
  | sg | sc | sm | scp | sbp | stt | sz1 | sz2 | sz3 | sz4 | sod | so1 | so2 | so3
  | se1 | se2 | se3 | sad | shf
  | tg | tc | tm | tcp | tbp | ttt | tend | tlen | tpar | tone | tzero | tad | thf
  | w0 | w1 | w2 | wg | wc | wm | wcp | wcb | wi1 | wi2 | wca | wrow | wrc | wrn | wcc
  | wrd | wcl | wcy | wby | wst
  | ak (k : Fin 3) | ak₁ (k : Fin 3) | ak₂ (k : Fin 3) | ak₃ (k : Fin 3)
  | acc | rej
  deriving DecidableEq, Fintype

open PathLabel

/-- The register added twice by add-twice loop `k`: `n`, `n`, the guessed vertex. -/
def akY : Fin 3 → Fin 9 := ![1, 1, 8]

/-- The exit of add-twice loop `k`. -/
def akEx : Fin 3 → PathLabel := ![wi1, wrn, wrd]

/-- **The walk machine** [AB09, §4.1.2]. Registers: `0` the input pointer `p`, `1` the vertex
count `n`, `2` and `3` counters `a`, `b`, `4` the source and then the current vertex, `5` the
target, `6` a scratch copy, `7` the step count, `8` the guessed next vertex. Deciders: `0`
reads an input bit, `1` compares with the input length.

* Unary scan: count the aligned `11` pairs into `n`, then expect `01`; `p = 2n + 2`.
* Matrix scan: aligned data pairs `00`/`11` counted by row `a` and column `b` (reset at `n`),
  inside the input; the separator `01` only after exactly `n²` pairs.
* Source and target: guess `s < n` (choose to stop or to increment), check the doubled field
  against the binary digits of `s` (parity and halving of a copy), then the separator;
  likewise `t < n` against the plain suffix, which must end the input.
* Walk: accept if the current vertex is `t`; reject after `n` steps; guess `v < n`, compute
  `p = 2n + 2 + 2(cur · n + v)` by add-twice loops, reject unless the input bit at `p` is `1`,
  move to `v`. -/
def pathA : NARM 9 2 PathLabel
  | u0 => .det (.call 0 .whole [0] u1 u2)
  | u1 => .det (.inc 0 u3)
  | u3 => .det (.call 0 .whole [0] u4 rej)
  | u4 => .det (.inc 0 u5)
  | u5 => .det (.inc 1 u0)
  | u2 => .det (.inc 0 u6)
  | u6 => .det (.call 0 .whole [0] u7 rej)
  | u7 => .det (.inc 0 m0)
  | m0 => .det (.call 1 .whole [0] mr rej)
  | mr => .det (.call 0 .whole [0] m1 m2)
  | m1 => .det (.inc 0 m3)
  | m3 => .det (.call 0 .whole [0] m5 rej)
  | m2 => .det (.inc 0 m4)
  | m4 => .det (.call 0 .whole [0] ms m5)
  | m5 => .det (.jeq 2 1 rej m7)
  | m7 => .det (.inc 0 m8)
  | m8 => .det (.inc 3 m9)
  | m9 => .det (.jeq 3 1 m10 m0)
  | m10 => .det (.clr 3 m11)
  | m11 => .det (.inc 2 m0)
  | ms => .det (.jeq 2 1 m12 rej)
  | m12 => .det (.inc 0 sg)
  | sg => .det (.jeq 4 1 rej sc)
  | sc => .choose scp sm
  | sm => .det (.inc 4 sg)
  | scp => .det (.jeq 6 4 stt sbp)
  | sbp => .det (.inc 6 scp)
  | stt => .det (.jz 6 sz1 sod)
  | sz1 => .det (.call 0 .whole [0] rej sz2)
  | sz2 => .det (.inc 0 sz3)
  | sz3 => .det (.call 0 .whole [0] sz4 rej)
  | sz4 => .det (.inc 0 tg)
  | sod => .det (.jodd 6 so1 se1)
  | so1 => .det (.call 0 .whole [0] so2 rej)
  | so2 => .det (.inc 0 so3)
  | so3 => .det (.call 0 .whole [0] sad rej)
  | se1 => .det (.call 0 .whole [0] rej se2)
  | se2 => .det (.inc 0 se3)
  | se3 => .det (.call 0 .whole [0] rej sad)
  | sad => .det (.inc 0 shf)
  | shf => .det (.half 6 stt)
  | tg => .det (.jeq 5 1 rej tc)
  | tc => .choose tcp tm
  | tm => .det (.inc 5 tg)
  | tcp => .det (.jeq 6 5 ttt tbp)
  | tbp => .det (.inc 6 tcp)
  | ttt => .det (.jz 6 tend tlen)
  | tend => .det (.call 1 .whole [0] rej w0)
  | tlen => .det (.call 1 .whole [0] tpar rej)
  | tpar => .det (.jodd 6 tone tzero)
  | tone => .det (.call 0 .whole [0] tad rej)
  | tzero => .det (.call 0 .whole [0] rej tad)
  | tad => .det (.inc 0 thf)
  | thf => .det (.half 6 ttt)
  | w0 => .det (.jeq 4 5 acc w1)
  | w1 => .det (.jeq 7 1 rej w2)
  | w2 => .det (.clr 8 wg)
  | wg => .det (.jeq 8 1 rej wc)
  | wc => .choose wcp wm
  | wm => .det (.inc 8 wg)
  | wcp => .det (.clr 0 wcb)
  | wcb => .det (.clr 3 (ak 0))
  | ak k => .det (.jeq 3 (akY k) (akEx k) (ak₁ k))
  | ak₁ k => .det (.inc 0 (ak₂ k))
  | ak₂ k => .det (.inc 0 (ak₃ k))
  | ak₃ k => .det (.inc 3 (ak k))
  | wi1 => .det (.inc 0 wi2)
  | wi2 => .det (.inc 0 wca)
  | wca => .det (.clr 2 wrow)
  | wrow => .det (.jeq 2 4 wcc wrc)
  | wrc => .det (.clr 3 (ak 1))
  | wrn => .det (.inc 2 wrow)
  | wcc => .det (.clr 3 (ak 2))
  | wrd => .det (.call 0 .whole [0] wcl rej)
  | wcl => .det (.clr 4 wcy)
  | wcy => .det (.jeq 4 8 wst wby)
  | wby => .det (.inc 4 wcy)
  | wst => .det (.inc 7 w0)
  | acc => .det (.ret true)
  | rej => .det (.ret false)

/-- **The machine meets the syntactic preconditions**: its comparisons are of distinct
registers and its calls have one argument. -/
lemma pathA_npreS (x : List Bool) (a : AConf 9 PathLabel) : NPreS pathA x a := by
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · cases l <;> simp [NPreS, PreS, NARM.detPart, pathA]
    all_goals (rename_i k; fin_cases k <;> simp [akY])

/-- The deciders of the walk machine: the input bit and input length languages. -/
def pathAs : Fin 2 → Language Bool := ![inputBitLang, inputLenLang]

/-- The deciders' answers. -/
noncomputable abbrev pathOr : Fin 2 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (pathAs j : Set (List Bool)) V

/-- Decider `0` reads an input bit. -/
lemma pathOr_bit (x : List Bool) (i : ℕ) :
    pathOr 0 (pairEncode x (Nat.bits i)) = x.getD i false := by
  simp [pathOr, pathAs, inputBitLang, indicator_indexLang_pairEncode]

/-- Decider `1` compares with the input length. -/
lemma pathOr_len (x : List Bool) (i : ℕ) :
    pathOr 1 (pairEncode x (Nat.bits i)) = decide (i < x.length) := by
  simp [pathOr, pathAs, inputLenLang, indicator_indexLang_pairEncode]

/-- The deciders are in `L`. -/
lemma pathAs_mem (j : Fin 2) : pathAs j ∈ LOGSPACE := by
  fin_cases j
  · exact inputBitLang_mem
  · exact inputLenLang_mem

/-- The register file of the walk machine, by name. -/
@[ext] structure PReg where
  /-- the input pointer (register `0`) -/
  p : ℕ
  /-- the vertex count (register `1`) -/
  n : ℕ
  /-- the row counter (register `2`) -/
  a : ℕ
  /-- the column counter (register `3`) -/
  b : ℕ
  /-- the source, then the current vertex (register `4`) -/
  s : ℕ
  /-- the target (register `5`) -/
  t : ℕ
  /-- the scratch copy (register `6`) -/
  tmp : ℕ
  /-- the step count (register `7`) -/
  st : ℕ
  /-- the guessed next vertex (register `8`) -/
  nx : ℕ

/-- The register values of a register file. -/
def PReg.v (σ : PReg) : Fin 9 → ℕ := ![σ.p, σ.n, σ.a, σ.b, σ.s, σ.t, σ.tmp, σ.st, σ.nx]

/-- Every register of a register file is at most `B`. -/
def PReg.Le (σ : PReg) (B : ℕ) : Prop :=
  σ.p ≤ B ∧ σ.n ≤ B ∧ σ.a ≤ B ∧ σ.b ≤ B ∧ σ.s ≤ B ∧ σ.t ≤ B ∧ σ.tmp ≤ B ∧ σ.st ≤ B ∧ σ.nx ≤ B

/-- The register-bound guard from the named bounds. -/
lemma PReg.reg {σ : PReg} {B : ℕ} (h : σ.Le B) (l : Option PathLabel) (res : Option Bool) :
    RegLe 9 PathLabel B (l, σ.v, res) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  intro r
  fin_cases r <;> assumption

section PRegSimp

variable (σ : PReg) (z : ℕ)

/-- Register `0` is the input pointer. -/
@[simp] lemma PReg.v_0 : σ.v 0 = σ.p := rfl
/-- Register `1` is the vertex count. -/
@[simp] lemma PReg.v_1 : σ.v 1 = σ.n := rfl
/-- Register `2` is the row counter. -/
@[simp] lemma PReg.v_2 : σ.v 2 = σ.a := rfl
/-- Register `3` is the column counter. -/
@[simp] lemma PReg.v_3 : σ.v 3 = σ.b := rfl
/-- Register `4` is the current vertex. -/
@[simp] lemma PReg.v_4 : σ.v 4 = σ.s := rfl
/-- Register `5` is the target. -/
@[simp] lemma PReg.v_5 : σ.v 5 = σ.t := rfl
/-- Register `6` is the scratch copy. -/
@[simp] lemma PReg.v_6 : σ.v 6 = σ.tmp := rfl
/-- Register `7` is the step count. -/
@[simp] lemma PReg.v_7 : σ.v 7 = σ.st := rfl
/-- Register `8` is the guessed vertex. -/
@[simp] lemma PReg.v_8 : σ.v 8 = σ.nx := rfl

/-- Writing register `0` writes the input pointer. -/
@[simp] lemma PReg.u_0 : Function.update σ.v 0 z = { σ with p := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `1` writes the vertex count. -/
@[simp] lemma PReg.u_1 : Function.update σ.v 1 z = { σ with n := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `2` writes the row counter. -/
@[simp] lemma PReg.u_2 : Function.update σ.v 2 z = { σ with a := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `3` writes the column counter. -/
@[simp] lemma PReg.u_3 : Function.update σ.v 3 z = { σ with b := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `4` writes the current vertex. -/
@[simp] lemma PReg.u_4 : Function.update σ.v 4 z = { σ with s := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `5` writes the target. -/
@[simp] lemma PReg.u_5 : Function.update σ.v 5 z = { σ with t := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `6` writes the scratch copy. -/
@[simp] lemma PReg.u_6 : Function.update σ.v 6 z = { σ with tmp := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `7` writes the step count. -/
@[simp] lemma PReg.u_7 : Function.update σ.v 7 z = { σ with st := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `8` writes the guessed vertex. -/
@[simp] lemma PReg.u_8 : Function.update σ.v 8 z = { σ with nx := z }.v := by
  funext r; fin_cases r <;> rfl

end PRegSimp

open PathLabel

/-- The semantics of the walk machine at label `l` with register file `σ`, registers
bounded by `B`. -/
abbrev PS (x : List Bool) (B : ℕ) (l : PathLabel) (σ : PReg) (P : Prop) : Prop :=
  NSem pathA pathOr x (RegLe 9 PathLabel B) (some l, σ.v, none) P

variable {x : List Bool} {B : ℕ}

/-- Change the register file to an equal one. -/
lemma PS.of_eq {l : PathLabel} {σ σ' : PReg} {P : Prop} (h : σ = σ') (hp : PS x B l σ' P) :
    PS x B l σ P := h ▸ hp

namespace PathWalkTac

/-- Normalize reads and updates of a named register file of the walk machine. -/
scoped macro "pw_regs" : tactic => `(tactic| simp only [PReg.v_0, PReg.v_1, PReg.v_2, PReg.v_3,
  PReg.v_4, PReg.v_5, PReg.v_6, PReg.v_7, PReg.v_8, PReg.u_0, PReg.u_1, PReg.u_2, PReg.u_3,
  PReg.u_4, PReg.u_5, PReg.u_6, PReg.u_7, PReg.u_8])

/-- Prove a register bound of the walk machine by linear arithmetic. -/
scoped macro "pw_le" : tactic => `(tactic| (simp only [PReg.Le] at *; omega))

/-- Prove an equality of register files field by field. -/
scoped macro "pw_ext" : tactic => `(tactic| (ext <;> dsimp only <;> omega))

/-- Prove an equality of register files field by field, simplifying first. -/
scoped macro "pw_ext'" : tactic => `(tactic| (ext <;> (try simp) <;> (try omega)))

end PathWalkTac

open PathWalkTac

/-- **The row loop** of the index computation: from row `a ≤ s` with the pointer at the
start of row `a`, the machine reaches the start of row `s`.

**Proof sketch.** Induction on `s - a`: at `a = s` the loop exits; otherwise it clears the
column counter, adds `2n` to the pointer (`nsem_addTwice`) and increments the row. All
pointer values stay below the start of row `s`, inside the input. -/
lemma ps_row (hB : 2 * x.length + 2 ≤ B) (P : Prop) (σ : PReg) (hσ : σ.Le B)
    (hi : σ.a ≤ σ.s) (hs : σ.s < σ.n) (hp : σ.p = 2 * σ.n + 2 + 2 * (σ.a * σ.n))
    (hb : σ.b ≤ σ.n) (hm : 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length)
    (hK : ∀ b', b' ≤ σ.n →
      PS x B wcc { σ with a := σ.s, p := 2 * σ.n + 2 + 2 * (σ.s * σ.n), b := b' } P) :
    PS x B wrow σ P := by
  suffices H : ∀ d (σ : PReg), σ.s - σ.a = d → σ.Le B → σ.a ≤ σ.s → σ.s < σ.n →
      σ.p = 2 * σ.n + 2 + 2 * (σ.a * σ.n) → σ.b ≤ σ.n →
      2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length →
      (∀ b', b' ≤ σ.n →
        PS x B wcc { σ with a := σ.s, p := 2 * σ.n + 2 + 2 * (σ.s * σ.n), b := b' } P) →
      PS x B wrow σ P from H _ σ rfl hσ hi hs hp hb hm hK
  intro d
  induction d with
  | zero =>
    intro σ hd hσ hi hs hp hb hm hK
    have he : σ.a = σ.s := by omega
    have he' : σ.a * σ.n = σ.s * σ.n := by rw [he]
    refine NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he) ?_
    exact PS.of_eq (by ext <;> simp <;> omega) (hK σ.b hb)
  | succ d ih =>
    intro σ hd hσ hi hs hp hb hm hK
    have hne : σ.a ≠ σ.s := by omega
    have h1 : (σ.a + 1) * σ.n ≤ σ.s * σ.n := Nat.mul_le_mul_right _ (by omega)
    have h2 : (σ.s + 1) * σ.n ≤ σ.n * σ.n := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1 h2
    refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using hne) ?_
    refine NSem.clr rfl (PReg.reg hσ _ _) ?_
    pw_regs
    refine nsem_addTwice pathA pathOr x B 3 1 0 (by decide) (by decide) (by decide)
      (ak 1) (ak₁ 1) (ak₂ 1) (ak₃ 1) wrn rfl rfl rfl rfl _ _ (PReg.reg (by pw_le) none none)
      (by simp) (by simp; omega) ?_
    pw_regs
    refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
    pw_regs
    refine PS.of_eq (σ' := { σ with a := σ.a + 1, p := σ.p + 2 * σ.n, b := σ.n })
      (by ext <;> simp) ?_
    exact ih _ (by dsimp only; omega) (by pw_le) (by dsimp only; omega) hs
      (by dsimp only; rw [Nat.add_mul, Nat.one_mul]; omega) le_rfl hm hK

/-- **The index computation**: the machine sets the pointer to the matrix position
`2n + 2 + 2(s · n + v)` of the edge from the current vertex `s` to the guessed vertex `v`.

**Proof sketch.** Clear the pointer, add `2n` (`nsem_addTwice`) and `2` to reach the
matrix, walk `s` rows (`ps_row`), then add `2v` (`nsem_addTwice`); the final position is
below `2n + 2 + 2n²`, inside the input (`rowMajor_lt`). -/
lemma ps_index (hB : 2 * x.length + 2 ≤ B) (P : Prop) (σ : PReg) (hσ : σ.Le B)
    (hs : σ.s < σ.n) (hj : σ.nx < σ.n) (hm : 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length)
    (hK : PS x B wrd
      { σ with p := 2 * σ.n + 2 + 2 * (σ.s * σ.n + σ.nx), a := σ.s, b := σ.nx } P) :
    PS x B wcp σ P := by
  have hidx := rowMajor_lt hs hj
  have h0 : σ.s * σ.n ≤ σ.n * σ.n := by omega
  refine NSem.clr rfl (PReg.reg hσ _ _) ?_
  pw_regs
  refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine nsem_addTwice pathA pathOr x B 3 1 0 (by decide) (by decide) (by decide)
    (ak 0) (ak₁ 0) (ak₂ 0) (ak₃ 0) wi1 rfl rfl rfl rfl _ _ (PReg.reg (by pw_le) none none)
    (by simp) (by simp; omega) ?_
  pw_regs
  refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine ps_row hB P _ (by pw_le) (by simp) (by simpa using hs) (by dsimp only; omega) (by simp)
    (by simpa using hm) fun b' hb' => ?_
  simp only at hb' ⊢
  refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
  pw_regs
  refine nsem_addTwice pathA pathOr x B 3 8 0 (by decide) (by decide) (by decide)
    (ak 2) (ak₁ 2) (ak₂ 2) (ak₃ 2) wrd rfl rfl rfl rfl _ _ (PReg.reg (by pw_le) none none)
    (by simp) (by simp; omega) ?_
  pw_regs
  exact PS.of_eq (by pw_ext') hK

/-- **The walk loop** [AB09, §4.1.2]: from the current vertex `s` after `st ≤ n` steps,
some branch accepts iff `t` is reachable from `s` within `n - st` edges; every branch
terminates.

**Proof sketch.** Induction on `n - st`. At `s = t` the machine accepts; at `st = n` it
rejects; otherwise it guesses `v < n` (`nsem_guess`), computes the matrix position
(`ps_index`), rejects unless the edge bit is `1`, copies `v` into the current vertex
(`nsem_copy`) and counts the step. -/
theorem ps_walk (hB : 2 * x.length + 2 ≤ B) (σ : PReg) (hσ : σ.Le B) (hs : σ.s < σ.n)
    (ht : σ.t < σ.n) (hst : σ.st ≤ σ.n) (hm : 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length) :
    PS x B w0 σ (WalkLe (pathEdge x σ.n) σ.n (σ.n - σ.st) σ.s σ.t) := by
  suffices H : ∀ d (σ : PReg), σ.n - σ.st = d → σ.Le B → σ.s < σ.n → σ.t < σ.n →
      σ.st ≤ σ.n → 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length →
      PS x B w0 σ (WalkLe (pathEdge x σ.n) σ.n d σ.s σ.t) from H _ σ rfl hσ hs ht hst hm
  intro d
  induction d with
  | zero =>
    intro σ hd hσ hs ht hst hm
    by_cases he : σ.s = σ.t
    · refine (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he)
        (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
      simp only [WalkLe, he]
    · refine (NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using he)
        (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simp; omega)
          (NSem.ret rfl (PReg.reg hσ _ _)))).congr ?_
      simp only [WalkLe, he, Bool.false_eq_true]
  | succ d ih =>
    intro σ hd hσ hs ht hst hm
    by_cases he : σ.s = σ.t
    · refine (NSem.jeq_pos rfl (PReg.reg hσ _ _) (by simpa using he)
        (NSem.ret rfl (PReg.reg hσ _ _))).congr ?_
      simp only [WalkLe, he, true_or]
    refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simpa using he) ?_
    refine NSem.jeq_neg rfl (PReg.reg hσ _ _) (by simp; omega) ?_
    refine NSem.clr rfl (PReg.reg hσ _ _) ?_
    pw_regs
    refine (nsem_guess pathA pathOr x B 8 1 (by decide) wg wc wm wcp rej rfl rfl rfl rfl
      (fun j => pathEdge x σ.n σ.s j ∧ WalkLe (pathEdge x σ.n) σ.n d j σ.t) _
      (PReg.reg (by pw_le) none none) (by simp) (fun j hj1 hj2 => ?_)).congr ?_
    · simp only [PReg.v_8, PReg.v_1] at hj1 hj2
      pw_regs
      have hidx := rowMajor_lt hs hj2
      refine ps_index hB _ _ (by pw_le) (by simpa using hs) (by simpa using hj2)
        (by simpa using hm) ?_
      simp only
      by_cases hedge : pathEdge x σ.n σ.s j
      · refine NSem.call_pos rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit]; exact hedge) ?_
        refine NSem.clr rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        refine nsem_copy pathA pathOr x B 4 8 (by decide) wcy wby wst rfl rfl _ _
          (PReg.reg (by pw_le) none none) (by simp) ?_
        pw_regs
        refine NSem.inc rfl (PReg.reg (by pw_le) _ _) ?_
        pw_regs
        let σ' : PReg :=
          ⟨2 * σ.n + 2 + 2 * (σ.s * σ.n + j), σ.n, σ.s, j, j, σ.t, σ.tmp, σ.st + 1, j⟩
        refine PS.of_eq (σ' := σ') (by simp only [σ']) ((ih σ' (by dsimp only [σ']; omega)
          (by simp only [σ', PReg.Le] at hσ ⊢; omega) (by dsimp only [σ']; omega) ht
          (by dsimp only [σ']; omega) hm).congr ?_)
        simp only [σ', hedge, true_and]
      · refine (NSem.call_neg rfl (PReg.reg (by pw_le) _ _)
          (by simp only [PReg.v_0, pathOr_bit]; simpa [pathEdge] using hedge)
          (NSem.ret rfl (PReg.reg (by pw_le) _ _))).congr ?_
        simp only [hedge, false_and, Bool.false_eq_true]
    · simp only [PReg.v_8, PReg.v_1, WalkLe, he, false_or]
      exact ⟨fun ⟨j, _, h⟩ => ⟨j, h.1, h.2⟩, fun ⟨j, h1, h2⟩ => ⟨j, Nat.zero_le _, h1, h2⟩⟩

end Complexity.LogProg
