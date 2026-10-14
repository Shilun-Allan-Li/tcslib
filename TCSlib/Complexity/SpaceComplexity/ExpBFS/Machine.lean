/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.MARMTime
import TCSlib.Complexity.SpaceComplexity.Machines.VWord
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The breadth-first search memory machine

The memory register machine `Complexity.LogProg.ExpBFS.A` deciding the language of a
nondeterministic space-bounded decider `N` in exponential time [AB09, §4.1.1, proof of
Theorem 4.2], over seventeen registers, a memory tape and four deciders: the input-length
decider and the initial, step and accepting code languages of `N`
(`TCSlib.Complexity.SpaceComplexity.Codec`). With `K₀ = codeK N`:

* **Setup**: `Lg := size |x| + 1` (an upper bound of `logSpace |x|`), `s := 0`.
* **Width** (phase `p`, radius `r = s` or `s + 1`): `w := K₀ (r + Lg + 1)`, `K := 2 ^ w` (a
  bound of the codes at radius `r`), and the memory base `Bs := 2K` (first search, final scan)
  or `K` (second search).
* **Search** (first at radius `s`, second at `s + 1`): mark at `Bs + u` the initial codes
  `u < K`; repeat rounds marking every unmarked `v < K` with a marked `u < K` and a step pair
  `(u, v)` until a round marks nothing; count the marked codes into `c`.
* **Iteration**: after the first search keep its count in `c1` and search at `s + 1`; if the
  counts agree, scan the first search's marks for an accepting code (accept iff one is found),
  else `s := s + 1` and repeat.

The memory is addressed by walking its head from cell `0` to `Bs + u` (counter `T`) and back
(counter `T2`). The regions `[2K, 3K)` of a first search and `[K, 2K)` of a second search are
disjoint from all earlier ones, since `K` grows by the factor `2 ^ K₀ ≥ 4` with the radius.

This file holds the machine and its register file; the run lemmas are in
`TCSlib.Complexity.SpaceComplexity.ExpBFS.Run`,
`TCSlib.Complexity.SpaceComplexity.ExpBFS.Relax` and
`TCSlib.Complexity.SpaceComplexity.ExpBFS.Search`.

Infrastructure for [AB09, §4.1.1, Theorem 4.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ExpBFS.St` — the register file.
* `Complexity.LogProg.ExpBFS.Lb` — the labels.
* `Complexity.LogProg.ExpBFS.A` — the machine.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Theorem 4.2.)
-/

namespace Complexity.LogProg

open Turing

namespace ExpBFS

/-! ## Registers -/
/-- Register `N`: the input length counter. -/
def rN : Fin 17 := 0
/-- Register `Lg`: the logarithm bound `size |x| + 1`. -/
def rLg : Fin 17 := 1
/-- Register `s`: the radius. -/
def rs : Fin 17 := 2
/-- Register `s1`: the next radius `s + 1`. -/
def rs1 : Fin 17 := 3
/-- Register `X`: the width factor `r + Lg + 1`. -/
def rX : Fin 17 := 4
/-- Register `w`: the code width. -/
def rw : Fin 17 := 5
/-- Register `K`: the code bound `2 ^ w`. -/
def rK : Fin 17 := 6
/-- Register `Bs`: the base of the memory region. -/
def rBs : Fin 17 := 7
/-- Register `U`: the source code. -/
def rU : Fin 17 := 8
/-- Register `V`: the target code. -/
def rV : Fin 17 := 9
/-- Register `T`: the outward walk counter. -/
def rT : Fin 17 := 10
/-- Register `T2`: the return walk counter. -/
def rT2 : Fin 17 := 11
/-- Register `Z`: the scratch register of the copy and shift loops. -/
def rZ : Fin 17 := 12
/-- Register `C`: the shift counter. -/
def rC : Fin 17 := 13
/-- Register `ch`: the change flag of a relaxation round. -/
def rch : Fin 17 := 14
/-- Register `c`: the count of marked codes. -/
def rc : Fin 17 := 15
/-- Register `c1`: the count of the first search. -/
def rc1 : Fin 17 := 16

/-- **The register file** of the search machine, by name. -/
@[ext] structure St where
  /-- the input length counter -/
  N : ℕ
  /-- the logarithm bound `size |x| + 1` -/
  Lg : ℕ
  /-- the radius -/
  s : ℕ
  /-- the next radius `s + 1` -/
  s1 : ℕ
  /-- the width factor `r + Lg + 1` -/
  X : ℕ
  /-- the code width -/
  w : ℕ
  /-- the code bound `2 ^ w` -/
  K : ℕ
  /-- the base of the memory region -/
  Bs : ℕ
  /-- the source code -/
  U : ℕ
  /-- the target code -/
  V : ℕ
  /-- the outward walk counter -/
  T : ℕ
  /-- the return walk counter -/
  T2 : ℕ
  /-- the scratch register of the copy and shift loops -/
  Z : ℕ
  /-- the shift counter -/
  C : ℕ
  /-- the change flag of a relaxation round -/
  ch : ℕ
  /-- the count of marked codes -/
  c : ℕ
  /-- the count of the first search -/
  c1 : ℕ

namespace St

/-- The register values of a register file, indexed as the machine's registers. -/
def toV (st : St) : Fin 17 → ℕ :=
  ![st.N, st.Lg, st.s, st.s1, st.X, st.w, st.K, st.Bs, st.U, st.V,
    st.T, st.T2, st.Z, st.C, st.ch, st.c, st.c1]

/-- The all-zero register file. -/
def zero : St := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The all-zero register file is the zero register valuation. -/
lemma toV_zero : (fun _ => 0 : Fin 17 → ℕ) = toV zero := by
  funext r; fin_cases r <;> rfl

/-- Reading register `N`. -/
@[simp] lemma toV_N (st : St) : st.toV rN = st.N := rfl
/-- Reading register `Lg`. -/
@[simp] lemma toV_Lg (st : St) : st.toV rLg = st.Lg := rfl
/-- Reading register `s`. -/
@[simp] lemma toV_s (st : St) : st.toV rs = st.s := rfl
/-- Reading register `s1`. -/
@[simp] lemma toV_s1 (st : St) : st.toV rs1 = st.s1 := rfl
/-- Reading register `X`. -/
@[simp] lemma toV_X (st : St) : st.toV rX = st.X := rfl
/-- Reading register `w`. -/
@[simp] lemma toV_w (st : St) : st.toV rw = st.w := rfl
/-- Reading register `K`. -/
@[simp] lemma toV_K (st : St) : st.toV rK = st.K := rfl
/-- Reading register `Bs`. -/
@[simp] lemma toV_Bs (st : St) : st.toV rBs = st.Bs := rfl
/-- Reading register `U`. -/
@[simp] lemma toV_U (st : St) : st.toV rU = st.U := rfl
/-- Reading register `V`. -/
@[simp] lemma toV_V (st : St) : st.toV rV = st.V := rfl
/-- Reading register `T`. -/
@[simp] lemma toV_T (st : St) : st.toV rT = st.T := rfl
/-- Reading register `T2`. -/
@[simp] lemma toV_T2 (st : St) : st.toV rT2 = st.T2 := rfl
/-- Reading register `Z`. -/
@[simp] lemma toV_Z (st : St) : st.toV rZ = st.Z := rfl
/-- Reading register `C`. -/
@[simp] lemma toV_C (st : St) : st.toV rC = st.C := rfl
/-- Reading register `ch`. -/
@[simp] lemma toV_ch (st : St) : st.toV rch = st.ch := rfl
/-- Reading register `c`. -/
@[simp] lemma toV_c (st : St) : st.toV rc = st.c := rfl
/-- Reading register `c1`. -/
@[simp] lemma toV_c1 (st : St) : st.toV rc1 = st.c1 := rfl
/-- Writing register `N`. -/
@[simp] lemma upd_N (st : St) (k : ℕ) :
    Function.update st.toV rN k = toV { st with N := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `Lg`. -/
@[simp] lemma upd_Lg (st : St) (k : ℕ) :
    Function.update st.toV rLg k = toV { st with Lg := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `s`. -/
@[simp] lemma upd_s (st : St) (k : ℕ) :
    Function.update st.toV rs k = toV { st with s := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `s1`. -/
@[simp] lemma upd_s1 (st : St) (k : ℕ) :
    Function.update st.toV rs1 k = toV { st with s1 := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `X`. -/
@[simp] lemma upd_X (st : St) (k : ℕ) :
    Function.update st.toV rX k = toV { st with X := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `w`. -/
@[simp] lemma upd_w (st : St) (k : ℕ) :
    Function.update st.toV rw k = toV { st with w := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `K`. -/
@[simp] lemma upd_K (st : St) (k : ℕ) :
    Function.update st.toV rK k = toV { st with K := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `Bs`. -/
@[simp] lemma upd_Bs (st : St) (k : ℕ) :
    Function.update st.toV rBs k = toV { st with Bs := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `U`. -/
@[simp] lemma upd_U (st : St) (k : ℕ) :
    Function.update st.toV rU k = toV { st with U := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `V`. -/
@[simp] lemma upd_V (st : St) (k : ℕ) :
    Function.update st.toV rV k = toV { st with V := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `T`. -/
@[simp] lemma upd_T (st : St) (k : ℕ) :
    Function.update st.toV rT k = toV { st with T := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `T2`. -/
@[simp] lemma upd_T2 (st : St) (k : ℕ) :
    Function.update st.toV rT2 k = toV { st with T2 := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `Z`. -/
@[simp] lemma upd_Z (st : St) (k : ℕ) :
    Function.update st.toV rZ k = toV { st with Z := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `C`. -/
@[simp] lemma upd_C (st : St) (k : ℕ) :
    Function.update st.toV rC k = toV { st with C := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `ch`. -/
@[simp] lemma upd_ch (st : St) (k : ℕ) :
    Function.update st.toV rch k = toV { st with ch := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `c`. -/
@[simp] lemma upd_c (st : St) (k : ℕ) :
    Function.update st.toV rc k = toV { st with c := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `c1`. -/
@[simp] lemma upd_c1 (st : St) (k : ℕ) :
    Function.update st.toV rc1 k = toV { st with c1 := k } := by
  funext r; fin_cases r <;> rfl

/-- All registers of the file are at most `B`. -/
def Bd (B : ℕ) (st : St) : Prop :=
  st.N ≤ B ∧ st.Lg ≤ B ∧ st.s ≤ B ∧ st.s1 ≤ B ∧ st.X ≤ B ∧ st.w ≤ B ∧ st.K ≤ B ∧ st.Bs ≤ B ∧
    st.U ≤ B ∧ st.V ≤ B ∧ st.T ≤ B ∧ st.T2 ≤ B ∧ st.Z ≤ B ∧ st.C ≤ B ∧ st.ch ≤ B ∧
    st.c ≤ B ∧ st.c1 ≤ B

/-- A bounded register file has bounded register values. -/
lemma Bd.toV {B : ℕ} {st : St} (h : st.Bd B) : ∀ r, st.toV r ≤ B := by
  obtain ⟨hN, hLg, hs, hs1, hX, hw, hK, hBs, hU, hV, hT, hT2, hZ, hC, hch, hc, hc1⟩ := h
  intro r; fin_cases r <;> assumption

end St

/-- Normalize register reads and writes of named register files. -/
scoped syntax "regs" (" [" (Lean.Parser.Tactic.simpLemma),* "]")? (Lean.Parser.Tactic.location)? :
  tactic
scoped macro_rules
  | `(tactic| regs $[$loc:location]?) =>
    `(tactic| simp only [St.toV_N, St.toV_Lg, St.toV_s, St.toV_s1, St.toV_X, St.toV_w, St.toV_K,
      St.toV_Bs, St.toV_U, St.toV_V, St.toV_T, St.toV_T2, St.toV_Z, St.toV_C,
      St.toV_ch, St.toV_c, St.toV_c1, St.upd_N, St.upd_Lg, St.upd_s, St.upd_s1,
      St.upd_X, St.upd_w, St.upd_K, St.upd_Bs, St.upd_U, St.upd_V, St.upd_T,
      St.upd_T2, St.upd_Z, St.upd_C, St.upd_ch, St.upd_c, St.upd_c1] $[$loc]?)
  | `(tactic| regs [$args,*] $[$loc:location]?) =>
    `(tactic| simp only [St.toV_N, St.toV_Lg, St.toV_s, St.toV_s1, St.toV_X, St.toV_w, St.toV_K,
      St.toV_Bs, St.toV_U, St.toV_V, St.toV_T, St.toV_T2, St.toV_Z, St.toV_C,
      St.toV_ch, St.toV_c, St.toV_c1, St.upd_N, St.upd_Lg, St.upd_s, St.upd_s1,
      St.upd_X, St.upd_w, St.upd_K, St.upd_Bs, St.upd_U, St.upd_V, St.upd_T,
      St.upd_T2, St.upd_Z, St.upd_C, St.upd_ch, St.upd_c, St.upd_c1,
      $args,*] $[$loc]?)


/-! ## Labels -/

/-- The phases of the width computation: the first search (radius `s`), the second search
(radius `s + 1`), the final scan (radius `s`). -/
inductive Ph3 where
  /-- the first search -/
  | fst
  /-- the second search -/
  | snd
  /-- the final scan -/
  | fin
  deriving DecidableEq, Fintype

/-- The radius register of a phase. -/
def rad : Ph3 → Fin 17
  | .snd => rs1
  | _ => rs

/-- The phase of a search (`false`: first, `true`: second). -/
def toPh (φ : Bool) : Ph3 := if φ then .snd else .fst

/-- The sites of the memory accesses. -/
inductive Site where
  /-- marking an initial code `U` -/
  | ini (φ : Bool)
  /-- reading the mark of `U` in a relaxation round -/
  | rU (φ : Bool)
  /-- reading the mark of `V` in a relaxation round -/
  | rV (φ : Bool)
  /-- marking `V` in a relaxation round -/
  | sV (φ : Bool)
  /-- reading the mark of `U` in the count -/
  | cU (φ : Bool)
  /-- reading the mark of `U` in the final scan -/
  | fU
  deriving DecidableEq, Fintype

/-- The index register of an access site. -/
def Site.idx : Site → Fin 17
  | .rV _ => ExpBFS.rV
  | .sV _ => ExpBFS.rV
  | _ => ExpBFS.rU

/-- Whether an access site sets the bit (else it reads it). -/
def Site.set : Site → Bool
  | .ini _ => true
  | .sV _ => true
  | _ => false

/-- The phases of a memory access after its two copies: the outward walk, the operation, the
return walk (carrying the bit read). -/
inductive AcPh where
  /-- the outward walk, phase `j` -/
  | wo (j : Fin 4)
  /-- the memory operation -/
  | op
  /-- the return walk with bit `b`, phase `j` -/
  | wb (b : Bool) (j : Fin 3)
  deriving DecidableEq, Fintype

/-- The sites of the copy loops (`src` is added to `dst` through `Z`; see `cpSrc`, `cpDst`). -/
inductive CpS (K₀ : ℕ) where
  /-- width: the radius into `X` -/
  | radX (p : Ph3)
  /-- width: `Lg` into `X` -/
  | lgX (p : Ph3)
  /-- width: the `i`-th addition of `X` into `w` -/
  | mw (p : Ph3) (i : Fin K₀)
  /-- width: `w` into the shift counter `C` -/
  | wC (p : Ph3)
  /-- width: `K` into the base `Bs` -/
  | KB1 (p : Ph3)
  /-- width: `K` into the base `Bs` once more (first search and final scan) -/
  | KB2 (p : Ph3)
  /-- access: the base `Bs` into `T` -/
  | aB (st : Site)
  /-- access: the index into `T` -/
  | aI (st : Site)
  /-- iteration: `s` into `s1` -/
  | s1
  deriving DecidableEq, Fintype

/-- **The labels of the search machine.** -/
inductive Lb (K₀ : ℕ) where
  /-- setup: query the input-length decider at `N` -/
  | scan
  /-- setup: increment `N` -/
  | incN
  /-- setup: `Lg := 1` -/
  | lgI
  /-- setup: test `N` -/
  | lg0
  /-- setup: halve `N` -/
  | lg1
  /-- setup: increment `Lg` -/
  | lg2
  /-- width: `X := X + 1` -/
  | wkI (p : Ph3)
  /-- width: clear `X` -/
  | wkC (p : Ph3)
  /-- width: `K := 1` -/
  | wkK (p : Ph3)
  /-- search: test `U = K` in the initial marking -/
  | iU (φ : Bool)
  /-- search: query the initial-code decider at `U` -/
  | iC (φ : Bool)
  /-- search: next `U` in the initial marking -/
  | iN (φ : Bool)
  /-- round: clear `U` -/
  | rl0 (φ : Bool)
  /-- round: clear the change flag -/
  | rlc (φ : Bool)
  /-- round: test `U = K` -/
  | rlU (φ : Bool)
  /-- round: test `V = K` -/
  | rlV (φ : Bool)
  /-- round: clear `V` after the inner loop -/
  | rlVZ (φ : Bool)
  /-- round: query the step decider at `(U, V)` -/
  | rlS (φ : Bool)
  /-- round: clear the change flag before raising it -/
  | rlH (φ : Bool)
  /-- round: raise the change flag -/
  | rlH2 (φ : Bool)
  /-- round: next `V` -/
  | rlNV (φ : Bool)
  /-- round: next `U` -/
  | rlNU (φ : Bool)
  /-- round: test the change flag -/
  | rlE (φ : Bool)
  /-- count: clear `U` -/
  | cn0 (φ : Bool)
  /-- count: test `U = K` -/
  | cnU (φ : Bool)
  /-- count: increment `c` -/
  | cnI (φ : Bool)
  /-- count: next `U` -/
  | cnN (φ : Bool)
  /-- after the first search: clear `U`, `V`, `w`, `K`, `Bs` -/
  | d1 (i : Fin 5)
  /-- after the first search: `s1 := s1 + 1` -/
  | s1i
  /-- after the second search: compare the counts -/
  | d2
  /-- before the final scan: clear `U`, `V`, `w`, `K`, `Bs` -/
  | fz (i : Fin 5)
  /-- next iteration: increment `s`, clear `U`, `V`, `w`, `K`, `Bs`, `c`, `c1`, `s1` -/
  | nz (i : Fin 9)
  /-- final scan: test `U = K` -/
  | fU
  /-- final scan: query the accepting-code decider at `U` -/
  | fA
  /-- final scan: next `U` -/
  | fN
  /-- accept -/
  | acc
  /-- reject -/
  | rej
  /-- a copy loop at site `k`, phase `j` -/
  | cp (k : CpS K₀) (j : Fin 7)
  /-- the move `c1 := c1 + c`, phase `j` -/
  | mv (j : Fin 3)
  /-- the shift `K := K · 2 ^ C` of phase `p`, step `j` -/
  | sh (p : Ph3) (j : Fin 9)
  /-- a memory access at site `st`, phase `ph` -/
  | ac (st : Site) (ph : AcPh)
  deriving DecidableEq, Fintype

variable {K₀ : ℕ}

/-! ## Loop sites -/

/-- The exit of the width computation of a phase. -/
def wkExit : Ph3 → Lb K₀
  | .fst => .iU false
  | .snd => .iU true
  | .fin => .fU

/-- The source register of a copy site. -/
def cpSrc : CpS K₀ → Fin 17
  | .radX p => rad p | .lgX _ => rLg | .mw _ _ => rX | .wC _ => rw | .KB1 _ => rK
  | .KB2 _ => rK | .aB _ => rBs | .aI st => st.idx | .s1 => rs

/-- The target register of a copy site. -/
def cpDst : CpS K₀ → Fin 17
  | .radX _ => rX | .lgX _ => rX | .mw _ _ => rw | .wC _ => rC | .KB1 _ => rBs
  | .KB2 _ => rBs | .aB _ => rT | .aI _ => rT | .s1 => rs1

/-- The exit label of a copy site. -/
def cpExit : CpS K₀ → Lb K₀
  | .radX p => .cp (.lgX p) 0
  | .lgX p => .wkI p
  | .mw p i => if h : i.val + 1 < K₀ then .cp (.mw p ⟨i.val + 1, h⟩) 0 else .wkC p
  | .wC p => .sh p 0
  | .KB1 p => if p = .snd then wkExit p else .cp (.KB2 p) 0
  | .KB2 p => wkExit p
  | .aB st => .cp (.aI st) 0
  | .aI st => .ac st (.wo 0)
  | .s1 => .s1i

/-- The exit of a memory access with the bit `b` read (or `true` after a set). -/
def acExit : Site → Bool → Lb K₀
  | .ini φ, _ => .iN φ
  | .rU φ, b => if b then .rlV φ else .rlNU φ
  | .rV φ, b => if b then .rlNV φ else .rlS φ
  | .sV φ, _ => .rlH φ
  | .cU φ, b => if b then .cnI φ else .cnN φ
  | .fU, b => if b then .fA else .fN

/-- The copy loops through `Z`. -/
def cpI (src dst : Fin 17) (ex : Lb K₀) (mk : Fin 7 → Lb K₀) (j : Fin 7) : Ins 17 4 (Lb K₀) :=
  match j.val with
  | 0 => .jz src (mk 4) (mk 1)
  | 1 => .dec src (mk 2)
  | 2 => .inc dst (mk 3)
  | 3 => .inc rZ (mk 0)
  | 4 => .jz rZ ex (mk 5)
  | 5 => .dec rZ (mk 6)
  | _ => .inc src (mk 4)

/-- The shift loops: `r := r · 2 ^ C` through `Z`. -/
def shI (r : Fin 17) (ex : Lb K₀) (mk : Fin 9 → Lb K₀) (j : Fin 9) : Ins 17 4 (Lb K₀) :=
  match j.val with
  | 0 => .jz rC ex (mk 1)
  | 1 => .dec rC (mk 2)
  | 2 => .jz r (mk 6) (mk 3)
  | 3 => .dec r (mk 4)
  | 4 => .inc rZ (mk 5)
  | 5 => .inc rZ (mk 2)
  | 6 => .jz rZ (mk 0) (mk 7)
  | 7 => .dec rZ (mk 8)
  | _ => .inc r (mk 6)

/-- The move loop `jz c; dec c; inc c1`. -/
def mvI (ex : Lb K₀) (j : Fin 3) : Ins 17 4 (Lb K₀) :=
  match j.val with
  | 0 => .jz rc ex (.mv 1)
  | 1 => .dec rc (.mv 2)
  | _ => .inc rc1 (.mv 0)

/-- The instructions of a memory access at site `st`: walk out counting `T` down and `T2` up,
read or set the bit, walk back counting `T2` down. -/
def acI (st : Site) : AcPh → MIns 17 4 (Lb K₀)
  | .wo j =>
    match j.val with
    | 0 => .det (.jz rT (.ac st .op) (.ac st (.wo 1)))
    | 1 => .det (.dec rT (.ac st (.wo 2)))
    | 2 => .det (.inc rT2 (.ac st (.wo 3)))
    | _ => .mright (.ac st (.wo 0))
  | .op => if st.set then .mset (.ac st (.wb true 0)) else
      .mread (.ac st (.wb true 0)) (.ac st (.wb false 0))
  | .wb b j =>
    match j.val with
    | 0 => .det (.jz rT2 (acExit st b) (.ac st (.wb b 1)))
    | 1 => .det (.dec rT2 (.ac st (.wb b 2)))
    | _ => .mleft (.ac st (.wb b 0))

/-- The registers cleared by the chains `d1`, `fz` (the first five) and `nz` (all eight). -/
def clrReg (i : ℕ) : Fin 17 :=
  match i with
  | 0 => rU | 1 => rV | 2 => rw | 3 => rK | 4 => rBs | 5 => rc | 6 => rc1 | _ => rs1

/-! ## The machine -/

/-- **The search machine** (code-width factor `K₀`): deciders `0` (input length), `1`
(initial codes), `2` (step pairs), `3` (accepting codes). See the module docstring. -/
def A (K₀ : ℕ) : MARM 17 4 (Lb K₀)
  | .scan => .det (.call 0 .whole [rN] .incN .lgI)
  | .incN => .det (.inc rN .scan)
  | .lgI => .det (.inc rLg .lg0)
  | .lg0 => .det (.jz rN (.cp (.radX .fst) 0) .lg1)
  | .lg1 => .det (.half rN .lg2)
  | .lg2 => .det (.inc rLg .lg0)
  | .wkI p => .det (.inc rX (if h : 0 < K₀ then .cp (.mw p ⟨0, h⟩) 0 else .wkC p))
  | .wkC p => .det (.clr rX (.wkK p))
  | .wkK p => .det (.inc rK (.cp (.wC p) 0))
  | .iU φ => .det (.jeq rU rK (.rl0 φ) (.iC φ))
  | .iC φ => .det (.call 1 .whole [rU, rad (toPh φ)] (.cp (.aB (.ini φ)) 0) (.iN φ))
  | .iN φ => .det (.inc rU (.iU φ))
  | .rl0 φ => .det (.clr rU (.rlc φ))
  | .rlc φ => .det (.clr rch (.rlU φ))
  | .rlU φ => .det (.jeq rU rK (.rlE φ) (.cp (.aB (.rU φ)) 0))
  | .rlV φ => .det (.jeq rV rK (.rlVZ φ) (.cp (.aB (.rV φ)) 0))
  | .rlVZ φ => .det (.clr rV (.rlNU φ))
  | .rlS φ => .det (.call 2 .whole [rU, rV, rad (toPh φ)] (.cp (.aB (.sV φ)) 0) (.rlNV φ))
  | .rlH φ => .det (.clr rch (.rlH2 φ))
  | .rlH2 φ => .det (.inc rch (.rlNV φ))
  | .rlNV φ => .det (.inc rV (.rlV φ))
  | .rlNU φ => .det (.inc rU (.rlU φ))
  | .rlE φ => .det (.jz rch (.cn0 φ) (.rl0 φ))
  | .cn0 φ => .det (.clr rU (.cnU φ))
  | .cnU φ => .det (.jeq rU rK (if φ then .d2 else .d1 0) (.cp (.aB (.cU φ)) 0))
  | .cnI φ => .det (.inc rc (.cnN φ))
  | .cnN φ => .det (.inc rU (.cnU φ))
  | .d1 i => .det (.clr (clrReg i.val)
      (if h : i.val + 1 < 5 then .d1 ⟨i.val + 1, h⟩ else .mv 0))
  | .s1i => .det (.inc rs1 (.cp (.radX .snd) 0))
  | .d2 => .det (.jeq rc rc1 (.fz 0) (.nz 0))
  | .fz i => .det (.clr (clrReg i.val)
      (if h : i.val + 1 < 5 then .fz ⟨i.val + 1, h⟩ else .cp (.radX .fin) 0))
  | .nz i => if i.val = 0 then .det (.inc rs (.nz 1)) else .det (.clr (clrReg (i.val - 1))
      (if h : i.val + 1 < 9 then .nz ⟨i.val + 1, h⟩ else .cp (.radX .fst) 0))
  | .fU => .det (.jeq rU rK .rej (.cp (.aB .fU) 0))
  | .fA => .det (.call 3 .whole [rU, rs] .acc .fN)
  | .fN => .det (.inc rU .fU)
  | .acc => .det (.ret true)
  | .rej => .det (.ret false)
  | .cp k j => .det (cpI (cpSrc k) (cpDst k) (cpExit k) (.cp k) j)
  | .mv j => .det (mvI (.cp .s1 0) j)
  | .sh p j => .det (shI rK (.cp (.KB1 p) 0) (.sh p) j)
  | .ac st ph => acI st ph

end ExpBFS

end Complexity.LogProg
