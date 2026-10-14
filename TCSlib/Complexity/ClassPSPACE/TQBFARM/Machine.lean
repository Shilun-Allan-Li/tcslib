/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Semantics
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidth
import TCSlib.Complexity.SpaceComplexity.Machines.VWord
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `TQBF` register machine

The abstract register machine `Complexity.LogProg.TQBFARM.A` evaluating quantified Boolean
formulas [AB09, §4.2, proof of Theorem 4.13], over seven registers and two deciders: the
input-bit and input-length deciders `Complexity.inputBitLang`, `Complexity.inputLenLang`,
through which it reads its own input at a register-held position. On input `x` it

1. runs the syntax automaton `Complexity.LogProg.TQBFARM.synStep` over `x` (labels `vl` …
   `vend`), answering `1` on a malformed input (which decodes to a true formula);
2. walks the tree of partial assignments depth first (labels `node` … `qU`): the depth is `K`,
   the assignment a binary stack `S` (`Complexity.LogProg.TQBFARM.asg`); a node at depth `K`
   reads the pair at input position `2K` — a doubled prefix bit (an inner node, quantifier
   `∃` for `1`) or the separator (a leaf); a finished node returns at `rt v`, which pops the
   stack and, by the quantifier of the parent, either returns again or descends into the
   second child;
3. at a leaf evaluates the CNF matrix (labels `leaf` … `lend`), streaming its serialization
   from position `2K + 2` and looking a literal's variable `V` up in the stack as bit
   `K - 1 - V` of `S` (a copy halved `K - 1 - V` times).

This file holds the machine, its register file `Complexity.LogProg.TQBFARM.St`, and the run
lemmas of its loop sites; the evaluation lemmas are in
`TCSlib.Complexity.ClassPSPACE.TQBFARM.Leaf` and `TCSlib.Complexity.ClassPSPACE.TQBFARM.Walk`.

Infrastructure for [AB09, §4.2, Theorem 4.13, membership half]; not itself a result of the
book.

## Main definitions

* `Complexity.LogProg.TQBFARM.Lb`, `Complexity.LogProg.TQBFARM.A` — the labels and the
  machine.
* `Complexity.LogProg.TQBFARM.St` — the register file.
* `Complexity.LogProg.TQBFARM.orc` — the deciders' answers.

## Main results

* `Complexity.LogProg.TQBFARM.orc_bit`, `orc_len` — the deciders read the input.
* `Complexity.LogProg.TQBFARM.cp_run`, `dm_run`, `mv_run`, `sb_run`, `hv_run` — the loop
  sites.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13.)
-/

namespace Complexity.LogProg

namespace TQBFARM

open Turing

/-! ## Deciders -/

/-- The deciders: `0` reads an input bit (`Complexity.inputBitLang`), `1` compares with the
input length (`Complexity.inputLenLang`). -/
def decs : Fin 2 → Language Bool := ![inputBitLang, inputLenLang]

/-- Both deciders are logspace. -/
lemma decs_mem (j : Fin 2) : decs j ∈ LOGSPACE := by
  fin_cases j
  · exact inputBitLang_mem
  · exact inputLenLang_mem

/-- The answers of the deciders. -/
noncomputable def orc : Fin 2 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (decs j : Set (List Bool)) V

/-- The bit decider reads the input. -/
lemma orc_bit (y : List Bool) (a : ℕ) : orc 0 (pairEncode y (Nat.bits a)) = y.getD a false := by
  show MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _
  rw [inputBitLang, indicator_indexLang_pairEncode]
  cases y.getD a false <;> simp

/-- The length decider compares with the input length. -/
lemma orc_len (y : List Bool) (a : ℕ) :
    orc 1 (pairEncode y (Nat.bits a)) = decide (a < y.length) := by
  show MultiTapeTM.indicator (inputLenLang : Set (List Bool)) _ = _
  rw [inputLenLang, indicator_indexLang_pairEncode]
  exact decide_eq_decide.mpr Iff.rfl

/-! ## Registers -/

/-- Register `K`: the depth. -/
def rK : Fin 7 := 0
/-- Register `S`: the assignment stack. -/
def rS : Fin 7 := 1
/-- Register `P`: the input pointer. -/
def rP : Fin 7 := 2
/-- Register `T`: a scratch copy of the stack. -/
def rT : Fin 7 := 3
/-- Register `Z`: the scratch register of the copy loops. -/
def rZ : Fin 7 := 4
/-- Register `C`: the halving counter. -/
def rC : Fin 7 := 5
/-- Register `V`: the variable of the current literal. -/
def rV : Fin 7 := 6

/-- **The register file** of the machine, by name. -/
@[ext] structure St where
  /-- the depth -/
  K : ℕ
  /-- the assignment stack -/
  S : ℕ
  /-- the input pointer -/
  P : ℕ
  /-- a scratch copy of the stack -/
  T : ℕ
  /-- the scratch register of the copy loops -/
  Z : ℕ
  /-- the halving counter -/
  C : ℕ
  /-- the variable of the current literal -/
  V : ℕ

namespace St

/-- The register values of a register file, indexed as the machine's registers. -/
def toV (st : St) : Fin 7 → ℕ := ![st.K, st.S, st.P, st.T, st.Z, st.C, st.V]

/-- The all-zero register file. -/
def zero : St := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- The all-zero register file is the zero register valuation. -/
lemma toV_zero : (fun _ => 0 : Fin 7 → ℕ) = toV zero := by
  funext r; fin_cases r <;> rfl

/-- Reading register `K`. -/
@[simp] lemma toV_K (st : St) : st.toV rK = st.K := rfl
/-- Reading register `S`. -/
@[simp] lemma toV_S (st : St) : st.toV rS = st.S := rfl
/-- Reading register `P`. -/
@[simp] lemma toV_P (st : St) : st.toV rP = st.P := rfl
/-- Reading register `T`. -/
@[simp] lemma toV_T (st : St) : st.toV rT = st.T := rfl
/-- Reading register `Z`. -/
@[simp] lemma toV_Z (st : St) : st.toV rZ = st.Z := rfl
/-- Reading register `C`. -/
@[simp] lemma toV_C (st : St) : st.toV rC = st.C := rfl
/-- Reading register `V`. -/
@[simp] lemma toV_V (st : St) : st.toV rV = st.V := rfl

/-- Writing register `K`. -/
@[simp] lemma upd_K (st : St) (k : ℕ) :
    Function.update st.toV rK k = toV { st with K := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `S`. -/
@[simp] lemma upd_S (st : St) (k : ℕ) :
    Function.update st.toV rS k = toV { st with S := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `P`. -/
@[simp] lemma upd_P (st : St) (k : ℕ) :
    Function.update st.toV rP k = toV { st with P := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `T`. -/
@[simp] lemma upd_T (st : St) (k : ℕ) :
    Function.update st.toV rT k = toV { st with T := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `Z`. -/
@[simp] lemma upd_Z (st : St) (k : ℕ) :
    Function.update st.toV rZ k = toV { st with Z := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `C`. -/
@[simp] lemma upd_C (st : St) (k : ℕ) :
    Function.update st.toV rC k = toV { st with C := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `V`. -/
@[simp] lemma upd_V (st : St) (k : ℕ) :
    Function.update st.toV rV k = toV { st with V := k } := by
  funext r; fin_cases r <;> rfl

/-- All registers of the file are at most `B`. -/
def Bd (B : ℕ) (st : St) : Prop :=
  st.K ≤ B ∧ st.S ≤ B ∧ st.P ≤ B ∧ st.T ≤ B ∧ st.Z ≤ B ∧ st.C ≤ B ∧ st.V ≤ B

/-- A bounded register file has bounded register values. -/
lemma Bd.toV {B : ℕ} {st : St} (h : st.Bd B) : ∀ r, st.toV r ≤ B := by
  obtain ⟨hK, hS, hP, hT, hZ, hC, hV⟩ := h
  intro r; fin_cases r <;> assumption

end St

/-- Normalize register reads and writes of named register files. -/
scoped syntax "regs" (" [" (Lean.Parser.Tactic.simpLemma),* "]")? (Lean.Parser.Tactic.location)? :
  tactic
scoped macro_rules
  | `(tactic| regs $[$loc:location]?) =>
    `(tactic| simp only [St.toV_K, St.toV_S, St.toV_P, St.toV_T, St.toV_Z, St.toV_C, St.toV_V,
      St.upd_K, St.upd_S, St.upd_P, St.upd_T, St.upd_Z, St.upd_C, St.upd_V] $[$loc]?)
  | `(tactic| regs [$args,*] $[$loc]?) =>
    `(tactic| simp only [St.toV_K, St.toV_S, St.toV_P, St.toV_T, St.toV_Z, St.toV_C, St.toV_V,
      St.upd_K, St.upd_S, St.upd_P, St.upd_T, St.upd_Z, St.upd_C, St.upd_V, $args,*] $[$loc]?)

/-! ## Labels -/

/-- The sites of the copy loops (`src` is added to `dst` through `Z`; see `cpSrc`, `cpDst`). -/
inductive CpS where
  /-- node: the first copy of `K` into the pointer `P` -/
  | ndA
  /-- node: the second copy of `K` into `P` (so `P = 2K`) -/
  | ndB
  /-- return: the first copy of `K` into `P`, carrying the child's value `v` -/
  | qA (v : Bool)
  /-- return: the second copy of `K` into `P` -/
  | qB (v : Bool)
  /-- literal: the depth `K` into the counter `C`, carrying the polarity `b` -/
  | lK (b : Bool)
  /-- literal: the stack `S` into the scratch `T` -/
  | lS (b : Bool)
  deriving DecidableEq, Fintype

/-- **The labels of the `TQBF` machine**: the syntax check (`init` … `vend`), the walk
(`node` … `qU`), the matrix evaluation (`leaf` … `lend`), and the loop families `cp`, `dm`,
`mv`, `sb`, `hv` (a site and a phase). -/
inductive Lb where
  /-- start: `S := 1` -/
  | init
  /-- syntax: ask whether `P < |x|` (automaton state `q`) -/
  | vl (q : SynSt)
  /-- syntax: read bit `P` -/
  | vr (q : SynSt)
  /-- syntax: advance after reading `b` -/
  | vs (q : SynSt) (b : Bool)
  /-- syntax: the input is consumed; accept a malformed input -/
  | vend (q : SynSt)
  /-- walk: a node; clear `P` -/
  | node
  /-- node: read bit `2K` -/
  | nd1
  /-- node: advance to bit `2K + 1` -/
  | nd2
  /-- node: read bit `2K + 1` -/
  | nd3
  /-- push the bit `b`: clear `P` -/
  | push (b : Bool)
  /-- push: the new bit `1` -/
  | incS
  /-- push: one level deeper -/
  | incK
  /-- return with value `v`: test for the root -/
  | rt (v : Bool)
  /-- the root's answer -/
  | fin (v : Bool)
  /-- return: one level up -/
  | pop (v : Bool)
  /-- return: test the last pushed bit -/
  | par (v : Bool)
  /-- return from a second child: pop -/
  | popT (v : Bool)
  /-- return from a first child: pop -/
  | popF (v : Bool)
  /-- return from a first child: read the quantifier at `2K` -/
  | qr (v : Bool)
  /-- an existential parent -/
  | qE (v : Bool)
  /-- a universal parent -/
  | qU (v : Bool)
  /-- leaf: advance to the matrix -/
  | leaf
  /-- matrix: read the next formula-level bit -/
  | fm
  /-- matrix: enter a clause -/
  | fmT
  /-- clause (satisfied so far: `s`): read the next bit -/
  | cl (s : Bool)
  /-- clause end -/
  | ce (s : Bool)
  /-- literal: skip its first `1` -/
  | lt (s : Bool)
  /-- literal: read the next bit of its unary variable -/
  | lc (s : Bool)
  /-- literal: count a `1` -/
  | lcT (s : Bool)
  /-- literal: advance after a `1` -/
  | lcI (s : Bool)
  /-- literal: advance past the terminator -/
  | lcF (s : Bool)
  /-- literal: read the polarity -/
  | lb (s : Bool)
  /-- literal: advance past the polarity `b` -/
  | lp (s b : Bool)
  /-- literal: evaluate unless the clause is already satisfied -/
  | lv (s b : Bool)
  /-- literal: test `C = K - V` (zero: the variable is free, reading `0`) -/
  | jzC (b : Bool)
  /-- literal: `C := K - 1 - V` -/
  | dc (b : Bool)
  /-- literal: test the variable's bit -/
  | od (b : Bool)
  /-- literal: the variable reads `1` -/
  | ot (b : Bool)
  /-- literal: the variable reads `0` -/
  | of (b : Bool)
  /-- matrix value `v`: clear `P` and return -/
  | lend (v : Bool)
  /-- a copy loop at site `k`, phase `j` -/
  | cp (k : CpS) (j : Fin 7)
  /-- the doubling move `T += 2 S` of a push, phase `j` -/
  | dm (b : Bool) (j : Fin 4)
  /-- the move `S += T` of a push, phase `j` -/
  | mv (b : Bool) (j : Fin 3)
  /-- the subtraction `C -= V` of a literal, phase `j` -/
  | sb (b : Bool) (j : Fin 3)
  /-- the halving `T := T / 2 ^ C` of a literal, phase `j` -/
  | hv (b : Bool) (j : Fin 3)
  deriving DecidableEq, Fintype

/-! ## Loop sites -/

/-- The source register of a copy site. -/
def cpSrc : CpS → Fin 7
  | .ndA => rK | .ndB => rK | .qA _ => rK | .qB _ => rK | .lK _ => rK | .lS _ => rS

/-- The target register of a copy site. -/
def cpDst : CpS → Fin 7
  | .ndA => rP | .ndB => rP | .qA _ => rP | .qB _ => rP | .lK _ => rC | .lS _ => rT

/-- The exit label of a copy site. -/
def cpExit : CpS → Lb
  | .ndA => .cp .ndB 0 | .ndB => .nd1 | .qA v => .cp (.qB v) 0 | .qB v => .qr v
  | .lK b => .sb b 0 | .lS b => .hv b 0

/-- The move loop `jz src; dec src; inc dst`. -/
def mvI (src dst : Fin 7) (ex : Lb) (mk : Fin 3 → Lb) (j : Fin 3) : Ins 7 2 Lb :=
  match j.val with
  | 0 => .jz src ex (mk 1)
  | 1 => .dec src (mk 2)
  | _ => .inc dst (mk 0)

/-- The doubled move loop `jz src; dec src; inc dst; inc dst`. -/
def dmI (src dst : Fin 7) (ex : Lb) (mk : Fin 4 → Lb) (j : Fin 4) : Ins 7 2 Lb :=
  match j.val with
  | 0 => .jz src ex (mk 1)
  | 1 => .dec src (mk 2)
  | 2 => .inc dst (mk 3)
  | _ => .inc dst (mk 0)

/-- The subtraction loop `jz q; dec q; dec r`. -/
def sbI (q r : Fin 7) (ex : Lb) (mk : Fin 3 → Lb) (j : Fin 3) : Ins 7 2 Lb :=
  match j.val with
  | 0 => .jz q ex (mk 1)
  | 1 => .dec q (mk 2)
  | _ => .dec r (mk 0)

/-- The halving loop `jz c; dec c; half r`. -/
def hvI (c r : Fin 7) (ex : Lb) (mk : Fin 3 → Lb) (j : Fin 3) : Ins 7 2 Lb :=
  match j.val with
  | 0 => .jz c ex (mk 1)
  | 1 => .dec c (mk 2)
  | _ => .half r (mk 0)

/-- The copy loops through `Z`. -/
def cpI (src dst : Fin 7) (ex : Lb) (mk : Fin 7 → Lb) (j : Fin 7) : Ins 7 2 Lb :=
  match j.val with
  | 0 => .jz src (mk 4) (mk 1)
  | 1 => .dec src (mk 2)
  | 2 => .inc dst (mk 3)
  | 3 => .inc rZ (mk 0)
  | 4 => .jz rZ ex (mk 5)
  | 5 => .dec rZ (mk 6)
  | _ => .inc src (mk 4)

/-! ## The machine -/

/-- **The `TQBF` machine**: deciders `0` (input bit) and `1` (input length); all reads are
`whole`-mode calls on the pointer `P`.

* Syntax: `S := 1`; for `P = 0, …, |x| - 1` step the automaton on bit `P`; at the end answer
  `1` unless the automaton is in state `inr 4`.
* Walk (`node`, at depth `K` with stack `S`): `P := 2K`; bit `P` is `1` (an `∃` level) →
  push `0`; else bit `P + 1` is `1` (the separator) → `leaf`; else (a `∀` level) push `0`.
  Push `b`: `S := 2S + b`, `K := K + 1`, back to `node`. Return `rt v`: at `K = 0` answer
  `v`; else `K := K - 1` and pop the bit `S mod 2`; after a second child return `v` again;
  after a first child read the quantifier at `2K` and return `v` if it is decisive (`1` at
  `∃`, `0` at `∀`), else push `1`.
* Leaf (`leaf`, at `P = 2K + 1`): stream the serialized matrix from `2K + 2`; a clause is
  satisfied when some literal `(V, b)` has `asg K S V = b`, where `C := K - V` is zero for a
  free variable (reading `0`), and otherwise `T := S / 2 ^ (C - 1)` is tested for oddness. -/
def A : ARM 7 2 Lb
  | .init => .inc rS (.vl (.inl none))
  | .vl q => .call 1 .whole [rP] (.vr q) (.vend q)
  | .vr q => .call 0 .whole [rP] (.vs q true) (.vs q false)
  | .vs q b => .inc rP (.vl (synStep q b))
  | .vend q => if q = .inr 4 then .clr rP .node else .ret true
  | .node => .clr rP (.cp .ndA 0)
  | .nd1 => .call 0 .whole [rP] (.push false) .nd2
  | .nd2 => .inc rP .nd3
  | .nd3 => .call 0 .whole [rP] .leaf (.push false)
  | .push b => .clr rP (.dm b 0)
  | .incS => .inc rS .incK
  | .incK => .inc rK .node
  | .rt v => .jz rK (.fin v) (.pop v)
  | .fin v => .ret v
  | .pop v => .dec rK (.par v)
  | .par v => .jodd rS (.popT v) (.popF v)
  | .popT v => .half rS (.rt v)
  | .popF v => .half rS (.cp (.qA v) 0)
  | .qr v => .call 0 .whole [rP] (.qE v) (.qU v)
  | .qE v => .clr rP (if v then .rt true else .push true)
  | .qU v => .clr rP (if v then .push true else .rt false)
  | .leaf => .inc rP .fm
  | .fm => .call 0 .whole [rP] .fmT (.lend true)
  | .fmT => .inc rP (.cl false)
  | .cl s => .call 0 .whole [rP] (.lt s) (.ce s)
  | .ce s => .inc rP (if s then .fm else .lend false)
  | .lt s => .inc rP (.lc s)
  | .lc s => .call 0 .whole [rP] (.lcT s) (.lcF s)
  | .lcT s => .inc rV (.lcI s)
  | .lcI s => .inc rP (.lc s)
  | .lcF s => .inc rP (.lb s)
  | .lb s => .call 0 .whole [rP] (.lp s true) (.lp s false)
  | .lp s b => .inc rP (.lv s b)
  | .lv s b => if s then .clr rV (.cl true) else .clr rT (.cp (.lK b) 0)
  | .jzC b => .jz rC (.cl (!b)) (.dc b)
  | .dc b => .dec rC (.cp (.lS b) 0)
  | .od b => .jodd rT (.ot b) (.of b)
  | .ot b => .clr rT (.cl b)
  | .of b => .clr rT (.cl (!b))
  | .lend v => .clr rP (.rt v)
  | .cp k j => cpI (cpSrc k) (cpDst k) (cpExit k) (.cp k) j
  | .dm b j => dmI rS rT (.mv b 0) (.dm b) j
  | .mv b j => mvI rT rS (if b then .incS else .incK) (.mv b) j
  | .sb b j => sbI rV rC (.jzC b) (.sb b) j
  | .hv b j => hvI rC rT (.od b) (.hv b) j

/-! ## Runs -/

variable {x : List Bool} {B : ℕ}

/-- **The machine meets the syntactic preconditions** everywhere: it has no equality tests,
and every call has the single argument `P`. -/
lemma preS_A (a : AConf 7 Lb) : PreS A x a := by
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · cases l with
    | vend q => by_cases h : q = .inr 4 <;> simp [PreS, A, h]
    | lv s b => cases s <;> simp [PreS, A]
    | cp k j => fin_cases j <;> simp [PreS, A, cpI]
    | dm b j => fin_cases j <;> simp [PreS, A, dmI]
    | mv b j => fin_cases j <;> simp [PreS, A, mvI]
    | sb b j => fin_cases j <;> simp [PreS, A, sbI]
    | hv b j => fin_cases j <;> simp [PreS, A, hvI]
    | qE v => cases v <;> simp [PreS, A]
    | qU v => cases v <;> simp [PreS, A]
    | ce s => cases s <;> simp [PreS, A]
    | _ => simp [PreS, A]

/-- Runs of the machine through bounded configurations. -/
abbrev Run (x : List Bool) (B : ℕ) (l : Lb) (st : St) (l' : Lb) (st' : St) : Prop :=
  AReach A orc x (GuardLe A x B) (some l, st.toV, none) (some l', st'.toV, none)

/-- A bounded register file at a label meets the guard. -/
lemma gb_of {st : St} (hbd : st.Bd B) (l : Lb) : GuardLe A x B (some l, st.toV, none) :=
  ⟨preS_A _, hbd.toV⟩

/-- One step from a bounded register file. -/
lemma step_of {st : St} {l : Lb} {c : AConf 7 Lb} (hbd : st.Bd B)
    (h : AReach A orc x (GuardLe A x B) (astep A orc x (some l, st.toV, none)) c) :
    AReach A orc x (GuardLe A x B) (some l, st.toV, none) c :=
  AReach.step (gb_of hbd l) h

/-- Close a run at an equal register file. -/
lemma fin_of {st st' : St} {l : Lb} (e : st = st') :
    AReach A orc x (GuardLe A x B) (some l, st.toV, none) (some l, st'.toV, none) :=
  e ▸ AReach.refl _

/-- Copy sites have distinct registers, all different from `Z`. -/
lemma cp_ne (k : CpS) : cpSrc k ≠ cpDst k ∧ cpSrc k ≠ rZ ∧ cpDst k ≠ rZ := by
  cases k <;> (try cases ‹Bool›) <;> decide

/-- **A copy site** adds the source to the target. -/
theorem cp_run (k : CpS) (st : St) (hbd : st.Bd B) (hZ : st.Z = 0)
    (hb : st.toV (cpDst k) + st.toV (cpSrc k) ≤ B) :
    AReach A orc x (GuardLe A x B) (some (.cp k 0), st.toV, none)
      (some (cpExit k), Function.update st.toV (cpDst k)
        (st.toV (cpDst k) + st.toV (cpSrc k)), none) :=
  copy_run (A := A) (oracle := orc) (x := x) (B := B) (l := .cp k 0) (l1 := .cp k 1)
    (l2 := .cp k 2) (l3 := .cp k 3) (l4 := .cp k 4) (l5 := .cp k 5) (l6 := .cp k 6)
    (lx := cpExit k) (cp_ne k).1 (cp_ne k).2.1 (cp_ne k).2.2 rfl rfl rfl rfl rfl rfl rfl _ hZ
    hbd.toV hb

/-- **The doubled move site** `T += 2 S`, `S := 0`. -/
theorem dm_run (b : Bool) (st : St) (hbd : st.Bd B) (hb : st.T + 2 * st.S ≤ B) :
    Run x B (.dm b 0) st (.mv b 0) { st with S := 0, T := st.T + 2 * st.S } := by
  have h := dmove_run (A := A) (oracle := orc) (x := x) (B := B) (r := rS) (t := rT)
    (l := .dm b 0) (l1 := .dm b 1) (l2 := .dm b 2) (l3 := .dm b 3) (lx := .mv b 0)
    (by decide) rfl rfl rfl rfl _ st.toV rfl hbd.toV hb
  regs at h
  exact h

/-- **The move site** `S += T`, `T := 0`. -/
theorem mv_run (b : Bool) (st : St) (hbd : st.Bd B) (hb : st.S + st.T ≤ B) :
    Run x B (.mv b 0) st (if b then .incS else .incK) { st with T := 0, S := st.S + st.T } := by
  have h := move_run (A := A) (oracle := orc) (x := x) (B := B) (r := rT) (t := rS)
    (l := .mv b 0) (l1 := .mv b 1) (l2 := .mv b 2) (lx := if b then .incS else .incK)
    (by decide) rfl rfl rfl _ st.toV rfl hbd.toV hb
  regs at h
  exact h

/-- **The subtraction site** `C := C - V`, `V := 0`. -/
theorem sb_run (b : Bool) (st : St) (hbd : st.Bd B) :
    Run x B (.sb b 0) st (.jzC b) { st with V := 0, C := st.C - st.V } := by
  have h := sub_run (A := A) (oracle := orc) (x := x) (B := B) (q := rV) (r := rC)
    (l := .sb b 0) (l1 := .sb b 1) (l2 := .sb b 2) (lx := .jzC b)
    (by decide) rfl rfl rfl _ st.toV rfl hbd.toV
  regs at h
  exact h

/-- **The halving site** `T := T / 2 ^ C`, `C := 0`. -/
theorem hv_run (b : Bool) (st : St) (hbd : st.Bd B) :
    Run x B (.hv b 0) st (.od b) { st with C := 0, T := st.T / 2 ^ st.C } := by
  have h := halve_run (A := A) (oracle := orc) (x := x) (B := B) (c := rC) (r := rT)
    (l := .hv b 0) (l1 := .hv b 1) (l2 := .hv b 2) (lx := .od b)
    (by decide) rfl rfl rfl _ st.toV rfl hbd.toV
  regs at h
  exact h

end TQBFARM

end Complexity.LogProg
