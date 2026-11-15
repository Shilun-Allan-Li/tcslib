/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHard
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider
import TCSlib.Complexity.SpaceComplexity.Logspace.QueryReshape
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The register file and the deciders of the `PATH`-reduction query machine

The interface of the query register machine `Complexity.PathHard.A`
(`TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine`) of the reduction
`Complexity.PathHard.red` [AB09, Theorem 4.18]: its fifteen named registers, the register
file `Complexity.PathHard.St` with its read/write simp lemmas, bounds and partial-update
identities, the tactic macros `regs`, `sbd`, `stp` (scoped in `Complexity.PathHard`), and the
five deciders it calls — the input bits and length, and the initial-, accepting- and
step-code languages of the decider `N` read through `Complexity.dropIdx` — with their
logspace membership and their answers.

Infrastructure for [AB09, §4.3, Theorem 4.18]; not itself a result of the book.

## Main definitions

* `Complexity.PathHard.St` — the register file; `St.toV`, `St.Bd`.
* `Complexity.PathHard.As`, `Complexity.PathHard.orc` — the deciders and their answers.

## Main results

* `Complexity.PathHard.St.eq_qk`, `Complexity.PathHard.St.eq_yid` — partial updates.
* `Complexity.PathHard.As_mem` — the deciders are logspace.
* `Complexity.PathHard.orc_bit`, `orc_len`, `orc_init`, `orc_acc`, `orc_step` — the
  deciders' answers.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Theorem 4.18.)
-/

namespace Complexity.PathHard

open Turing LogProg

/-! ## Registers -/

/-- Register `y`: the query length, then the decoding pointer. -/
abbrev rY : Fin 15 := 0
/-- Register `p`: the pair-scan pointer, then the start `2|x| + 2` of the index field. -/
abbrev rP : Fin 15 := 1
/-- Register `x`: the length `|x|`. -/
abbrev rX : Fin 15 := 2
/-- Register `t`: a scratch register. -/
abbrev rT : Fin 15 := 3
/-- Register `c`: the loop counter. -/
abbrev rC : Fin 15 := 4
/-- Register `s`: the radius. -/
abbrev rS : Fin 15 := 5
/-- Register `e`: the vertex exponent `E`. -/
abbrev rE : Fin 15 := 6
/-- Register `n`: `2n = 2 ^ (E + 1)`. -/
abbrev rN : Fin 15 := 7
/-- Register `m`: `2n² = 2 ^ (2E + 1)`. -/
abbrev rM : Fin 15 := 8
/-- Register `k`: the width cap `4n²`. -/
abbrev rK : Fin 15 := 9
/-- Register `q`: the pointer of the width check. -/
abbrev rQ : Fin 15 := 10
/-- Register `i`: the decoded index, then the remaining offset. -/
abbrev rI : Fin 15 := 11
/-- Register `d`: the scratch register of decoding and comparison. -/
abbrev rD : Fin 15 := 12
/-- Register `u`: the source vertex. -/
abbrev rU : Fin 15 := 13
/-- Register `z`: the scratch register of the shift loops. -/
abbrev rZ : Fin 15 := 14

/-- **The register file** of the query machine, by name. -/
@[ext] structure St where
  /-- the query length, then the decoding pointer -/
  y : ℕ
  /-- the pair-scan pointer -/
  p : ℕ
  /-- the length `|x|` -/
  x : ℕ
  /-- a scratch register -/
  t : ℕ
  /-- the loop counter -/
  c : ℕ
  /-- the radius -/
  s : ℕ
  /-- the vertex exponent -/
  e : ℕ
  /-- `2n` -/
  n : ℕ
  /-- `2n²` -/
  m : ℕ
  /-- the width cap -/
  k : ℕ
  /-- the pointer of the width check -/
  q : ℕ
  /-- the index, then the remaining offset -/
  i : ℕ
  /-- the decoding and comparison scratch -/
  d : ℕ
  /-- the source vertex -/
  u : ℕ
  /-- the shift scratch -/
  z : ℕ

namespace St

/-- The register values of a register file. -/
def toV (st : St) : Fin 15 → ℕ :=
  ![st.y, st.p, st.x, st.t, st.c, st.s, st.e, st.n, st.m, st.k, st.q, st.i, st.d, st.u, st.z]

/-- The all-zero register file. -/
def zero : St := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The all-zero register file is the zero valuation. -/
lemma toV_zero : (fun _ => 0 : Fin 15 → ℕ) = toV zero := by
  funext r; fin_cases r <;> rfl

/-- Reading register `y`. -/
@[simp] lemma toV_y (st : St) : st.toV rY = st.y := rfl
/-- Reading register `p`. -/
@[simp] lemma toV_p (st : St) : st.toV rP = st.p := rfl
/-- Reading register `x`. -/
@[simp] lemma toV_x (st : St) : st.toV rX = st.x := rfl
/-- Reading register `t`. -/
@[simp] lemma toV_t (st : St) : st.toV rT = st.t := rfl
/-- Reading register `c`. -/
@[simp] lemma toV_c (st : St) : st.toV rC = st.c := rfl
/-- Reading register `s`. -/
@[simp] lemma toV_s (st : St) : st.toV rS = st.s := rfl
/-- Reading register `e`. -/
@[simp] lemma toV_e (st : St) : st.toV rE = st.e := rfl
/-- Reading register `n`. -/
@[simp] lemma toV_n (st : St) : st.toV rN = st.n := rfl
/-- Reading register `m`. -/
@[simp] lemma toV_m (st : St) : st.toV rM = st.m := rfl
/-- Reading register `k`. -/
@[simp] lemma toV_k (st : St) : st.toV rK = st.k := rfl
/-- Reading register `q`. -/
@[simp] lemma toV_q (st : St) : st.toV rQ = st.q := rfl
/-- Reading register `i`. -/
@[simp] lemma toV_i (st : St) : st.toV rI = st.i := rfl
/-- Reading register `d`. -/
@[simp] lemma toV_d (st : St) : st.toV rD = st.d := rfl
/-- Reading register `u`. -/
@[simp] lemma toV_u (st : St) : st.toV rU = st.u := rfl
/-- Reading register `z`. -/
@[simp] lemma toV_z (st : St) : st.toV rZ = st.z := rfl

/-- Writing register `y`. -/
@[simp] lemma upd_y (st : St) (v : ℕ) : Function.update st.toV rY v = toV { st with y := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `p`. -/
@[simp] lemma upd_p (st : St) (v : ℕ) : Function.update st.toV rP v = toV { st with p := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `x`. -/
@[simp] lemma upd_x (st : St) (v : ℕ) : Function.update st.toV rX v = toV { st with x := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `t`. -/
@[simp] lemma upd_t (st : St) (v : ℕ) : Function.update st.toV rT v = toV { st with t := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `c`. -/
@[simp] lemma upd_c (st : St) (v : ℕ) : Function.update st.toV rC v = toV { st with c := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `s`. -/
@[simp] lemma upd_s (st : St) (v : ℕ) : Function.update st.toV rS v = toV { st with s := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `e`. -/
@[simp] lemma upd_e (st : St) (v : ℕ) : Function.update st.toV rE v = toV { st with e := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `n`. -/
@[simp] lemma upd_n (st : St) (v : ℕ) : Function.update st.toV rN v = toV { st with n := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `m`. -/
@[simp] lemma upd_m (st : St) (v : ℕ) : Function.update st.toV rM v = toV { st with m := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `k`. -/
@[simp] lemma upd_k (st : St) (v : ℕ) : Function.update st.toV rK v = toV { st with k := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `q`. -/
@[simp] lemma upd_q (st : St) (v : ℕ) : Function.update st.toV rQ v = toV { st with q := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `i`. -/
@[simp] lemma upd_i (st : St) (v : ℕ) : Function.update st.toV rI v = toV { st with i := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `d`. -/
@[simp] lemma upd_d (st : St) (v : ℕ) : Function.update st.toV rD v = toV { st with d := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `u`. -/
@[simp] lemma upd_u (st : St) (v : ℕ) : Function.update st.toV rU v = toV { st with u := v } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `z`. -/
@[simp] lemma upd_z (st : St) (v : ℕ) : Function.update st.toV rZ v = toV { st with z := v } := by
  funext r; fin_cases r <;> rfl

/-- All registers of the file are at most `B`. -/
def Bd (B : ℕ) (st : St) : Prop :=
  st.y ≤ B ∧ st.p ≤ B ∧ st.x ≤ B ∧ st.t ≤ B ∧ st.c ≤ B ∧ st.s ≤ B ∧ st.e ≤ B ∧ st.n ≤ B ∧
    st.m ≤ B ∧ st.k ≤ B ∧ st.q ≤ B ∧ st.i ≤ B ∧ st.d ≤ B ∧ st.u ≤ B ∧ st.z ≤ B

/-- A bounded register file has bounded register values. -/
lemma Bd.toV {B : ℕ} {st : St} (h : st.Bd B) : ∀ r, st.toV r ≤ B := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  intro r; fin_cases r <;> assumption

/-- A register file whose values are bounded is bounded. -/
lemma Bd.of_toV {B : ℕ} {st : St} (h : ∀ r, st.toV r ≤ B) : st.Bd B :=
  ⟨h rY, h rP, h rX, h rT, h rC, h rS, h rE, h rN, h rM, h rK, h rQ, h rI, h rD, h rU, h rZ⟩

/-- A valuation agreeing with a register file outside `q` and `k` is that file with `q` and
`k` replaced. -/
lemma eq_qk (st : St) (v : Fin 15 → ℕ) (h : ∀ r, r ≠ rQ → r ≠ rK → v r = st.toV r) :
    v = toV { st with q := v rQ, k := v rK } := by
  funext r
  fin_cases r
  · show v rY = st.y; exact (h rY (by decide) (by decide)).trans (St.toV_y st)
  · show v rP = st.p; exact (h rP (by decide) (by decide)).trans (St.toV_p st)
  · show v rX = st.x; exact (h rX (by decide) (by decide)).trans (St.toV_x st)
  · show v rT = st.t; exact (h rT (by decide) (by decide)).trans (St.toV_t st)
  · show v rC = st.c; exact (h rC (by decide) (by decide)).trans (St.toV_c st)
  · show v rS = st.s; exact (h rS (by decide) (by decide)).trans (St.toV_s st)
  · show v rE = st.e; exact (h rE (by decide) (by decide)).trans (St.toV_e st)
  · show v rN = st.n; exact (h rN (by decide) (by decide)).trans (St.toV_n st)
  · show v rM = st.m; exact (h rM (by decide) (by decide)).trans (St.toV_m st)
  · show v rK = v rK; rfl
  · show v rQ = v rQ; rfl
  · show v rI = st.i; exact (h rI (by decide) (by decide)).trans (St.toV_i st)
  · show v rD = st.d; exact (h rD (by decide) (by decide)).trans (St.toV_d st)
  · show v rU = st.u; exact (h rU (by decide) (by decide)).trans (St.toV_u st)
  · show v rZ = st.z; exact (h rZ (by decide) (by decide)).trans (St.toV_z st)

/-- A valuation agreeing with a register file outside `y`, `i` and `d` is that file with
`y`, `i` and `d` replaced. -/
lemma eq_yid (st : St) (v : Fin 15 → ℕ) (h : ∀ r, r ≠ rY → r ≠ rI → r ≠ rD → v r = st.toV r) :
    v = toV { st with y := v rY, i := v rI, d := v rD } := by
  funext r
  fin_cases r
  · show v rY = v rY; rfl
  · show v rP = st.p; exact (h rP (by decide) (by decide) (by decide)).trans (St.toV_p st)
  · show v rX = st.x; exact (h rX (by decide) (by decide) (by decide)).trans (St.toV_x st)
  · show v rT = st.t; exact (h rT (by decide) (by decide) (by decide)).trans (St.toV_t st)
  · show v rC = st.c; exact (h rC (by decide) (by decide) (by decide)).trans (St.toV_c st)
  · show v rS = st.s; exact (h rS (by decide) (by decide) (by decide)).trans (St.toV_s st)
  · show v rE = st.e; exact (h rE (by decide) (by decide) (by decide)).trans (St.toV_e st)
  · show v rN = st.n; exact (h rN (by decide) (by decide) (by decide)).trans (St.toV_n st)
  · show v rM = st.m; exact (h rM (by decide) (by decide) (by decide)).trans (St.toV_m st)
  · show v rK = st.k; exact (h rK (by decide) (by decide) (by decide)).trans (St.toV_k st)
  · show v rQ = st.q; exact (h rQ (by decide) (by decide) (by decide)).trans (St.toV_q st)
  · show v rI = v rI; rfl
  · show v rD = v rD; rfl
  · show v rU = st.u; exact (h rU (by decide) (by decide) (by decide)).trans (St.toV_u st)
  · show v rZ = st.z; exact (h rZ (by decide) (by decide) (by decide)).trans (St.toV_z st)

end St

/-- Normalize register reads and writes of named register files. -/
scoped syntax "regs" (" [" (Lean.Parser.Tactic.simpLemma),* "]")? (Lean.Parser.Tactic.location)? :
  tactic
scoped macro_rules
  | `(tactic| regs $[$loc:location]?) =>
    `(tactic| simp only [St.toV_y, St.toV_p, St.toV_x, St.toV_t, St.toV_c, St.toV_s, St.toV_e,
      St.toV_n, St.toV_m, St.toV_k, St.toV_q, St.toV_i, St.toV_d, St.toV_u, St.toV_z,
      St.upd_y, St.upd_p, St.upd_x, St.upd_t, St.upd_c, St.upd_s, St.upd_e, St.upd_n, St.upd_m,
      St.upd_k, St.upd_q, St.upd_i, St.upd_d, St.upd_u, St.upd_z] $[$loc]?)
  | `(tactic| regs [$args,*] $[$loc:location]?) =>
    `(tactic| simp only [St.toV_y, St.toV_p, St.toV_x, St.toV_t, St.toV_c, St.toV_s, St.toV_e,
      St.toV_n, St.toV_m, St.toV_k, St.toV_q, St.toV_i, St.toV_d, St.toV_u, St.toV_z,
      St.upd_y, St.upd_p, St.upd_x, St.upd_t, St.upd_c, St.upd_s, St.upd_e, St.upd_n, St.upd_m,
      St.upd_k, St.upd_q, St.upd_i, St.upd_d, St.upd_u, St.upd_z, $args,*] $[$loc]?)

set_option hygiene false in
/-- Close a bound on a register file. -/
scoped macro "sbd" : tactic => `(tactic| (simp only [St.Bd] at hbd ⊢ <;> omega))

set_option hygiene false in
/-- Normalize one step of the query machine (after `step_of`/`stepH_of`). -/
scoped macro "stp" : tactic =>
  `(tactic| simp only [astep, A, St.toV_y, St.toV_p, St.toV_x, St.toV_t, St.toV_c, St.toV_s,
      St.toV_e, St.toV_n, St.toV_m, St.toV_k, St.toV_q, St.toV_i, St.toV_d, St.toV_u, St.toV_z,
      St.upd_y, St.upd_p, St.upd_x, St.upd_t, St.upd_c, St.upd_s, St.upd_e, St.upd_n, St.upd_m,
      St.upd_k, St.upd_q, St.upd_i, St.upd_d, St.upd_u, St.upd_z, ↓reduceIte,
      Nat.add_one_ne_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, one_ne_zero,
      Nat.zero_add, Nat.add_zero, Bool.false_eq_true, ↓reduceDIte])

/-! ## The deciders -/

/-- **The deciders**: the input bits and length (`0`, `1`), and the initial-, accepting- and
step-code languages of `N` read through `dropIdx` (`2`, `3`, `4`). -/
def As (N : FinNDTM Bool) : Fin 5 → Language Bool :=
  ![inputBitLang, inputLenLang, {z | dropIdx z ∈ Codec.initLang N},
    {z | dropIdx z ∈ Codec.acceptLang N}, {z | dropIdx z ∈ Codec.stepLang N}]

/-- The deciders are logspace: the code languages are (`Complexity.Codec.initLang_mem`, …),
and `dropIdx` is implicitly logspace computable. -/
lemma As_mem (N : FinNDTM Bool) (j : Fin 5) : As N j ∈ LOGSPACE := by
  fin_cases j
  · exact inputBitLang_mem
  · exact inputLenLang_mem
  · exact mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx Codec.initLang_mem
  · exact mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx Codec.acceptLang_mem
  · exact mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx Codec.stepLang_mem

/-- The oracle answering the machine's calls. -/
noncomputable def orc (N : FinNDTM Bool) : Fin 5 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (As N j : Set (List Bool)) V

/-- Decider `0` reads the query. -/
lemma orc_bit (N : FinNDTM Bool) (y : List Bool) (p : ℕ) :
    orc N 0 (pairEncode y (Nat.bits p)) = y.getD p false := by
  simp only [orc, As, Matrix.cons_val_zero, inputBitLang, indicator_indexLang_pairEncode]
  cases y.getD p false <;> simp

/-- Decider `1` compares with the query length. -/
lemma orc_len (N : FinNDTM Bool) (y : List Bool) (p : ℕ) :
    orc N 1 (pairEncode y (Nat.bits p)) = decide (p < y.length) := by
  simp only [orc, As, Matrix.cons_val_one, Matrix.cons_val_zero, inputLenLang,
    indicator_indexLang_pairEncode]
  exact decide_eq_decide.mpr Iff.rfl

/-- Decider `2` answers the initial-code language on `⟨x, ⟨bits v, bits s⟩⟩`. -/
lemma orc_init (N : FinNDTM Bool) (x β : List Bool) (v s : ℕ) :
    orc N 2 (pairEncode (pairEncode x β) (pairEncode (Nat.bits v) (Nat.bits s))) =
      @decide (pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ Codec.initLang N)
        (Classical.dec _) := by
  simp only [orc, As, indicator_eq_decide]
  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode])

/-- Decider `3` answers the accepting-code language on `⟨x, ⟨bits u, bits s⟩⟩`. -/
lemma orc_acc (N : FinNDTM Bool) (x β : List Bool) (u s : ℕ) :
    orc N 3 (pairEncode (pairEncode x β) (pairEncode (Nat.bits u) (Nat.bits s))) =
      @decide (pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ Codec.acceptLang N)
        (Classical.dec _) := by
  simp only [orc, As, indicator_eq_decide]
  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode])

/-- Decider `4` answers the step relation. -/
lemma orc_step (N : FinNDTM Bool) (x β : List Bool) (u v s : ℕ) :
    orc N 4 (pairEncode (pairEncode x β)
        (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits s)))) =
      @decide (Codec.StepRel N x s u v) (Classical.dec _) := by
  simp only [orc, As, indicator_eq_decide]
  exact decide_eq_decide.mpr (by simp [dropIdx_pairEncode, Codec.StepRel])

end Complexity.PathHard
