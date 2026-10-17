/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.SpaceComplexity.Machines.NARMKit
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The register file of the inductive-counting machine

The seventeen named registers of the window-growing inductive-counting machine
`Complexity.LogProg.ISGen.igA` of Immerman and Szelepcsényi [AB09, §4.3.2, proof of Theorem
4.20, and Corollary 4.21], run on the configuration graph of a nondeterministic decider `N`
whose vertices are the codes of `TCSlib.Complexity.SpaceComplexity.Codec`: the register file
`Complexity.LogProg.ISCount.St` with its read/write simp lemmas and register bound, the
site-indexed registers of the walks and of the setup rounds, the step, initial-code and
accepting-code tests read from the four deciders of the Savitch machine
(`Complexity.LogProg.SavitchARM.decs`), and the tactic macros `isr` / `isb` (scoped in
`Complexity.LogProg.ISCount.ISTac`).

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ISCount.St` — the register file; `St.toV`, `St.Bd`, `St.Clear`.
* `Complexity.LogProg.ISCount.rY`, `Complexity.LogProg.ISCount.wT`,
  `Complexity.LogProg.ISCount.wB`, `St.wt`, `St.wb` — site-indexed registers.
* `Complexity.LogProg.ISCount.RelO`, `Complexity.LogProg.ISCount.InitO`,
  `Complexity.LogProg.ISCount.AccO` — the tests read from the deciders.
* `Complexity.LogProg.ISCount.lgv` — the halving count `size |x| + 1`.

## Main results

* `Complexity.LogProg.ISCount.St.toV_zero` — the all-zero register file is the zero
  valuation.
* the simp lemmas `St.toV_n`, …, `St.toV_stp` (reads) and `St.upd_n`, …, `St.upd_stp`
  (writes) of the register file.
* `Complexity.LogProg.ISCount.toV_wT`, `toV_wB`, `toV_rY` — reading the site-indexed
  registers.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20.)
-/

namespace Complexity.LogProg

namespace ISCount

open Turing

/-! ## Registers -/

/-- Register `n`: the input length (halved to `0` by the setup). -/
def rn : Fin 17 := 0
/-- Register `lg`: the halving count `size |x| + 1`. -/
def rlg : Fin 17 := 1
/-- Register `k`: the counter of the add-twice loops. -/
def rk : Fin 17 := 2
/-- Register `s`: the window radius. -/
def rs : Fin 17 := 3
/-- Register `e`: the exponent of the code bound. -/
def re : Fin 17 := 4
/-- Register `K`: the code bound. -/
def rK : Fin 17 := 5
/-- Register `T`: the doubling scratch register. -/
def rT : Fin 17 := 6
/-- Register `i`: the stage (the radius of the known ball). -/
def ri : Fin 17 := 7
/-- Register `i1`: the stage plus one. -/
def ri1 : Fin 17 := 8
/-- Register `cp`: the size of the known ball. -/
def rcp : Fin 17 := 9
/-- Register `v`: the vertex of the outer enumeration. -/
def rv : Fin 17 := 10
/-- Register `c`: the count of the next ball. -/
def rc : Fin 17 := 11
/-- Register `u`: the vertex of the inner enumeration. -/
def ru : Fin 17 := 12
/-- Register `cnt`: the count of the inner enumeration. -/
def rcnt : Fin 17 := 13
/-- Register `g`: the guessed code. -/
def rg : Fin 17 := 14
/-- Register `cur`: the current code of a walk. -/
def rcur : Fin 17 := 15
/-- Register `stp`: the step count of a walk. -/
def rstp : Fin 17 := 16

/-- **The register file** of the counting machine, by name. -/
@[ext] structure St where
  /-- the input length -/
  n : ℕ
  /-- the halving count -/
  lg : ℕ
  /-- the add-twice counter -/
  k : ℕ
  /-- the window radius -/
  s : ℕ
  /-- the exponent of the code bound -/
  e : ℕ
  /-- the code bound -/
  K : ℕ
  /-- the doubling scratch register -/
  T : ℕ
  /-- the stage -/
  i : ℕ
  /-- the stage plus one -/
  i1 : ℕ
  /-- the size of the known ball -/
  cp : ℕ
  /-- the outer vertex -/
  v : ℕ
  /-- the count of the next ball -/
  c : ℕ
  /-- the inner vertex -/
  u : ℕ
  /-- the inner count -/
  cnt : ℕ
  /-- the guessed code -/
  g : ℕ
  /-- the current code of a walk -/
  cur : ℕ
  /-- the step count of a walk -/
  stp : ℕ

namespace St

/-- The register values of a register file, indexed as the machine's registers. -/
def toV (σ : St) : Fin 17 → ℕ :=
  ![σ.n, σ.lg, σ.k, σ.s, σ.e, σ.K, σ.T, σ.i, σ.i1, σ.cp, σ.v, σ.c, σ.u, σ.cnt, σ.g, σ.cur,
    σ.stp]

/-- The all-zero register file. -/
def zero : St := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The all-zero register file is the zero valuation. -/
lemma toV_zero : zero.toV = fun _ => 0 := by
  funext r; fin_cases r <;> rfl

variable (σ : St) (z : ℕ)

/-- Reading `n`. -/
@[simp] lemma toV_n : σ.toV rn = σ.n := rfl
/-- Reading `lg`. -/
@[simp] lemma toV_lg : σ.toV rlg = σ.lg := rfl
/-- Reading `k`. -/
@[simp] lemma toV_k : σ.toV rk = σ.k := rfl
/-- Reading `s`. -/
@[simp] lemma toV_s : σ.toV rs = σ.s := rfl
/-- Reading `e`. -/
@[simp] lemma toV_e : σ.toV re = σ.e := rfl
/-- Reading `K`. -/
@[simp] lemma toV_K : σ.toV rK = σ.K := rfl
/-- Reading `T`. -/
@[simp] lemma toV_T : σ.toV rT = σ.T := rfl
/-- Reading `i`. -/
@[simp] lemma toV_i : σ.toV ri = σ.i := rfl
/-- Reading `i1`. -/
@[simp] lemma toV_i1 : σ.toV ri1 = σ.i1 := rfl
/-- Reading `cp`. -/
@[simp] lemma toV_cp : σ.toV rcp = σ.cp := rfl
/-- Reading `v`. -/
@[simp] lemma toV_v : σ.toV rv = σ.v := rfl
/-- Reading `c`. -/
@[simp] lemma toV_c : σ.toV rc = σ.c := rfl
/-- Reading `u`. -/
@[simp] lemma toV_u : σ.toV ru = σ.u := rfl
/-- Reading `cnt`. -/
@[simp] lemma toV_cnt : σ.toV rcnt = σ.cnt := rfl
/-- Reading `g`. -/
@[simp] lemma toV_g : σ.toV rg = σ.g := rfl
/-- Reading `cur`. -/
@[simp] lemma toV_cur : σ.toV rcur = σ.cur := rfl
/-- Reading `stp`. -/
@[simp] lemma toV_stp : σ.toV rstp = σ.stp := rfl

/-- Writing `n`. -/
@[simp] lemma upd_n : Function.update σ.toV rn z = toV { σ with n := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `lg`. -/
@[simp] lemma upd_lg : Function.update σ.toV rlg z = toV { σ with lg := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `k`. -/
@[simp] lemma upd_k : Function.update σ.toV rk z = toV { σ with k := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `s`. -/
@[simp] lemma upd_s : Function.update σ.toV rs z = toV { σ with s := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `e`. -/
@[simp] lemma upd_e : Function.update σ.toV re z = toV { σ with e := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `K`. -/
@[simp] lemma upd_K : Function.update σ.toV rK z = toV { σ with K := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `T`. -/
@[simp] lemma upd_T : Function.update σ.toV rT z = toV { σ with T := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `i`. -/
@[simp] lemma upd_i : Function.update σ.toV ri z = toV { σ with i := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `i1`. -/
@[simp] lemma upd_i1 : Function.update σ.toV ri1 z = toV { σ with i1 := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `cp`. -/
@[simp] lemma upd_cp : Function.update σ.toV rcp z = toV { σ with cp := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `v`. -/
@[simp] lemma upd_v : Function.update σ.toV rv z = toV { σ with v := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `c`. -/
@[simp] lemma upd_c : Function.update σ.toV rc z = toV { σ with c := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `u`. -/
@[simp] lemma upd_u : Function.update σ.toV ru z = toV { σ with u := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `cnt`. -/
@[simp] lemma upd_cnt : Function.update σ.toV rcnt z = toV { σ with cnt := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `g`. -/
@[simp] lemma upd_g : Function.update σ.toV rg z = toV { σ with g := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `cur`. -/
@[simp] lemma upd_cur : Function.update σ.toV rcur z = toV { σ with cur := z } := by
  funext r; fin_cases r <;> rfl
/-- Writing `stp`. -/
@[simp] lemma upd_stp : Function.update σ.toV rstp z = toV { σ with stp := z } := by
  funext r; fin_cases r <;> rfl

/-- Every register of the file is at most `B`. -/
def Bd (B : ℕ) (σ : St) : Prop :=
  σ.n ≤ B ∧ σ.lg ≤ B ∧ σ.k ≤ B ∧ σ.s ≤ B ∧ σ.e ≤ B ∧ σ.K ≤ B ∧ σ.T ≤ B ∧ σ.i ≤ B ∧
    σ.i1 ≤ B ∧ σ.cp ≤ B ∧ σ.v ≤ B ∧ σ.c ≤ B ∧ σ.u ≤ B ∧ σ.cnt ≤ B ∧ σ.g ≤ B ∧ σ.cur ≤ B ∧
    σ.stp ≤ B

end St

/-! ## Site-indexed registers -/

/-- The register added twice in a setup round: `lg` (`false`) or `s` (`true`). -/
def rY (ph : Bool) : Fin 17 := if ph then rs else rlg

/-- The target of a walk: `v` (outer site) or `u` (inner site). -/
def wT (b : Bool) : Fin 17 := if b then ru else rv

/-- The step bound of a walk: `i1` (outer site) or `i` (inner site). -/
def wB (b : Bool) : Fin 17 := if b then ri else ri1

/-- Reading the target of a walk. -/
@[simp] lemma toV_wT (σ : St) (b : Bool) : σ.toV (wT b) = if b then σ.u else σ.v := by
  cases b <;> rfl

/-- Reading the step bound of a walk. -/
@[simp] lemma toV_wB (σ : St) (b : Bool) : σ.toV (wB b) = if b then σ.i else σ.i1 := by
  cases b <;> rfl

/-- Reading the added register of a round. -/
@[simp] lemma toV_rY (σ : St) (ph : Bool) : σ.toV (rY ph) = if ph then σ.s else σ.lg := by
  cases ph <;> rfl

/-- The target of the walk at site `b`: `u` (inner) or `v` (outer). -/
def St.wt (b : Bool) (σ : St) : ℕ := if b then σ.u else σ.v

/-- The step bound of the walk at site `b`: `i` (inner) or `i1` (outer). -/
def St.wb (b : Bool) (σ : St) : ℕ := if b then σ.i else σ.i1

/-- The scratch registers of the walks and of the inner enumeration are clear. -/
def St.Clear (σ : St) : Prop := σ.g = 0 ∧ σ.cur = 0 ∧ σ.stp = 0 ∧ σ.u = 0 ∧ σ.cnt = 0

/-- The halving count `size |x| + 1` computed by the setup. -/
def lgv (n : ℕ) : ℕ := Nat.size n + 1

/-! ## The tests read from the deciders -/

/-- The step relation read from the step decider at radius `s`. -/
abbrev RelO (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s : ℕ) : ℕ → ℕ → Prop :=
  SavitchARM.Rel orc x s

/-- The initial-code test read from the initial-code decider at radius `s`. -/
abbrev InitO (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s : ℕ) : ℕ → Prop :=
  SavitchARM.InitO orc x s

/-- The accepting-code test read from the accepting-code decider at radius `s`. -/
abbrev AccO (orc : Fin 4 → List Bool → Bool) (x : List Bool) (s : ℕ) : ℕ → Prop :=
  SavitchARM.AccO orc x s

/-! ## Tactics -/

namespace ISTac

/-- Normalize reads and writes of named register files of the counting machine. -/
scoped macro "isr" : tactic => `(tactic| simp only [St.toV_n, St.toV_lg, St.toV_k, St.toV_s,
  St.toV_e, St.toV_K, St.toV_T, St.toV_i, St.toV_i1, St.toV_cp, St.toV_v, St.toV_c, St.toV_u,
  St.toV_cnt, St.toV_g, St.toV_cur, St.toV_stp, St.upd_n, St.upd_lg, St.upd_k, St.upd_s,
  St.upd_e, St.upd_K, St.upd_T, St.upd_i, St.upd_i1, St.upd_cp, St.upd_v, St.upd_c, St.upd_u,
  St.upd_cnt, St.upd_g, St.upd_cur, St.upd_stp])

/-- Prove a register bound of the counting machine by linear arithmetic. -/
scoped macro "isb" : tactic => `(tactic| (simp only [St.Bd] at *; omega))

end ISTac

end ISCount

end Complexity.LogProg
