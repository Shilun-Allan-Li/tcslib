/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidth
import TCSlib.Complexity.SpaceComplexity.Machines.VWord
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Savitch register machine

The abstract register machine `Complexity.LogProg.SavitchARM.A` of Savitch's algorithm
[AB09, §4.2.1, proof of Theorem 4.14], over eighteen registers and four deciders: the
input-length decider and the initial, accepting and step code languages of a
nondeterministic decider (`TCSlib.Complexity.SpaceComplexity.Codec`). On input `x`, with
`n = |x|` and a constant `E`, it computes the radius `s = (n + 2) ^ E`, the code width
`w = (n + 2) ^ (2E)` and the code bound `K = 2 ^ w` by arithmetic loops, then searches for an
initial code `u < K` and an accepting code `v < K` with `Reach K R w u v`, evaluating the
midpoint recursion with an explicit stack: saved endpoints are pushed as `w`-bit digits of
the register `SE` (shift left by `w`, add), phase bits as binary digits of `SP`.

This file holds the machine, its register file `Complexity.LogProg.SavitchARM.St`, and the
bookkeeping lemmas; the run lemmas are in `TCSlib.Complexity.SpaceComplexity.SavitchARM.Run`,
`TCSlib.Complexity.SpaceComplexity.SavitchARM.Recursion`,
`TCSlib.Complexity.SpaceComplexity.SavitchARM.Setup` and
`TCSlib.Complexity.SpaceComplexity.SavitchARM.Search`.

## Main definitions

* `Complexity.LogProg.SavitchARM.Lb` — the labels.
* `Complexity.LogProg.SavitchARM.A` — the machine.
* `Complexity.LogProg.SavitchARM.St`, `Complexity.LogProg.SavitchARM.St.toV` — the
  register file.

## Main results

* `Complexity.LogProg.SavitchARM.St.Bd.toV` — a register file bounded field by field is
  bounded as a valuation (the form of the guard `Complexity.LogProg.GuardLe`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14.)
-/

namespace Complexity.LogProg

open Turing

namespace SavitchARM

/-! ## Registers -/
/-- Register `n`: the input length counter. -/
def rn : Fin 18 := 0
/-- Register `a`: the base `|x| + 2`. -/
def ra : Fin 18 := 1
/-- Register `X`: the exponent counter. -/
def rX : Fin 18 := 2
/-- Register `P`: the power accumulator. -/
def rP : Fin 18 := 3
/-- Register `T`: a scratch register. -/
def rT : Fin 18 := 4
/-- Register `Z`: the scratch register of the copy and shift loops. -/
def rZ : Fin 18 := 5
/-- Register `C`: the loop counter. -/
def rC : Fin 18 := 6
/-- Register `s`: the window radius. -/
def rs : Fin 18 := 7
/-- Register `w`: the code width (also the recursion depth). -/
def rw : Fin 18 := 8
/-- Register `K`: the code bound `2 ^ w`. -/
def rK : Fin 18 := 9
/-- Register `U`: the source code of the current node. -/
def rU : Fin 18 := 10
/-- Register `V`: the target code of the current node. -/
def rV : Fin 18 := 11
/-- Register `M`: the midpoint of the current node. -/
def rM : Fin 18 := 12
/-- Register `I`: the level of the current node. -/
def rI : Fin 18 := 13
/-- Register `SE`: the stack of saved endpoints (`w`-bit digits). -/
def rSE : Fin 18 := 14
/-- Register `SP`: the stack of phase bits. -/
def rSP : Fin 18 := 15
/-- Register `E`: the endpoint popped last. -/
def rE : Fin 18 := 16
/-- Register `Q`: a scratch register of the pop routine. -/
def rQ : Fin 18 := 17

/-- **The register file** of the Savitch machine, by name. -/
@[ext] structure St where
  /-- the input length counter -/
  n : ℕ
  /-- the base `|x| + 2` -/
  a : ℕ
  /-- the exponent counter -/
  X : ℕ
  /-- the power accumulator -/
  P : ℕ
  /-- a scratch register -/
  T : ℕ
  /-- the scratch register of the copy and shift loops -/
  Z : ℕ
  /-- the loop counter -/
  C : ℕ
  /-- the window radius -/
  s : ℕ
  /-- the code width (also the recursion depth) -/
  w : ℕ
  /-- the code bound `2 ^ w` -/
  K : ℕ
  /-- the source code of the current node -/
  U : ℕ
  /-- the target code of the current node -/
  V : ℕ
  /-- the midpoint of the current node -/
  M : ℕ
  /-- the level of the current node -/
  I : ℕ
  /-- the stack of saved endpoints (`w`-bit digits) -/
  SE : ℕ
  /-- the stack of phase bits -/
  SP : ℕ
  /-- the endpoint popped last -/
  E : ℕ
  /-- a scratch register of the pop routine -/
  Q : ℕ

namespace St

/-- The register values of a register file, indexed as the machine's registers. -/
def toV (st : St) : Fin 18 → ℕ :=
  ![st.n, st.a, st.X, st.P, st.T, st.Z, st.C, st.s, st.w, st.K, st.U, st.V, st.M, st.I, st.SE,
    st.SP, st.E, st.Q]

/-- The all-zero register file. -/
def zero : St := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The all-zero register file is the zero register valuation. -/
lemma toV_zero : (fun _ => 0 : Fin 18 → ℕ) = toV zero := by
  funext r; fin_cases r <;> rfl

/-- Reading register `n`. -/
@[simp] lemma toV_n (st : St) : st.toV rn = st.n := rfl
/-- Reading register `a`. -/
@[simp] lemma toV_a (st : St) : st.toV ra = st.a := rfl
/-- Reading register `X`. -/
@[simp] lemma toV_X (st : St) : st.toV rX = st.X := rfl
/-- Reading register `P`. -/
@[simp] lemma toV_P (st : St) : st.toV rP = st.P := rfl
/-- Reading register `T`. -/
@[simp] lemma toV_T (st : St) : st.toV rT = st.T := rfl
/-- Reading register `Z`. -/
@[simp] lemma toV_Z (st : St) : st.toV rZ = st.Z := rfl
/-- Reading register `C`. -/
@[simp] lemma toV_C (st : St) : st.toV rC = st.C := rfl
/-- Reading register `s`. -/
@[simp] lemma toV_s (st : St) : st.toV rs = st.s := rfl
/-- Reading register `w`. -/
@[simp] lemma toV_w (st : St) : st.toV rw = st.w := rfl
/-- Reading register `K`. -/
@[simp] lemma toV_K (st : St) : st.toV rK = st.K := rfl
/-- Reading register `U`. -/
@[simp] lemma toV_U (st : St) : st.toV rU = st.U := rfl
/-- Reading register `V`. -/
@[simp] lemma toV_V (st : St) : st.toV rV = st.V := rfl
/-- Reading register `M`. -/
@[simp] lemma toV_M (st : St) : st.toV rM = st.M := rfl
/-- Reading register `I`. -/
@[simp] lemma toV_I (st : St) : st.toV rI = st.I := rfl
/-- Reading register `SE`. -/
@[simp] lemma toV_SE (st : St) : st.toV rSE = st.SE := rfl
/-- Reading register `SP`. -/
@[simp] lemma toV_SP (st : St) : st.toV rSP = st.SP := rfl
/-- Reading register `E`. -/
@[simp] lemma toV_E (st : St) : st.toV rE = st.E := rfl
/-- Reading register `Q`. -/
@[simp] lemma toV_Q (st : St) : st.toV rQ = st.Q := rfl

/-- Writing register `n`. -/
@[simp] lemma upd_n (st : St) (k : ℕ) :
    Function.update st.toV rn k = toV { st with n := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `a`. -/
@[simp] lemma upd_a (st : St) (k : ℕ) :
    Function.update st.toV ra k = toV { st with a := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `X`. -/
@[simp] lemma upd_X (st : St) (k : ℕ) :
    Function.update st.toV rX k = toV { st with X := k } := by
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
/-- Writing register `s`. -/
@[simp] lemma upd_s (st : St) (k : ℕ) :
    Function.update st.toV rs k = toV { st with s := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `w`. -/
@[simp] lemma upd_w (st : St) (k : ℕ) :
    Function.update st.toV rw k = toV { st with w := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `K`. -/
@[simp] lemma upd_K (st : St) (k : ℕ) :
    Function.update st.toV rK k = toV { st with K := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `U`. -/
@[simp] lemma upd_U (st : St) (k : ℕ) :
    Function.update st.toV rU k = toV { st with U := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `V`. -/
@[simp] lemma upd_V (st : St) (k : ℕ) :
    Function.update st.toV rV k = toV { st with V := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `M`. -/
@[simp] lemma upd_M (st : St) (k : ℕ) :
    Function.update st.toV rM k = toV { st with M := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `I`. -/
@[simp] lemma upd_I (st : St) (k : ℕ) :
    Function.update st.toV rI k = toV { st with I := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `SE`. -/
@[simp] lemma upd_SE (st : St) (k : ℕ) :
    Function.update st.toV rSE k = toV { st with SE := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `SP`. -/
@[simp] lemma upd_SP (st : St) (k : ℕ) :
    Function.update st.toV rSP k = toV { st with SP := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `E`. -/
@[simp] lemma upd_E (st : St) (k : ℕ) :
    Function.update st.toV rE k = toV { st with E := k } := by
  funext r; fin_cases r <;> rfl
/-- Writing register `Q`. -/
@[simp] lemma upd_Q (st : St) (k : ℕ) :
    Function.update st.toV rQ k = toV { st with Q := k } := by
  funext r; fin_cases r <;> rfl

/-- All registers of the file are at most `B`. -/
def Bd (B : ℕ) (st : St) : Prop :=
  st.n ≤ B ∧ st.a ≤ B ∧ st.X ≤ B ∧ st.P ≤ B ∧ st.T ≤ B ∧ st.Z ≤ B ∧ st.C ≤ B ∧ st.s ≤ B ∧
    st.w ≤ B ∧ st.K ≤ B ∧ st.U ≤ B ∧ st.V ≤ B ∧ st.M ≤ B ∧ st.I ≤ B ∧ st.SE ≤ B ∧ st.SP ≤ B ∧
    st.E ≤ B ∧ st.Q ≤ B

/-- A bounded register file has bounded register values. -/
lemma Bd.toV {B : ℕ} {st : St} (h : st.Bd B) : ∀ r, st.toV r ≤ B := by
  obtain ⟨hn, ha, hX, hP, hT, hZ, hC, hs, hw, hK, hU, hV, hM, hI, hSE, hSP, hE, hQ⟩ := h
  intro r; fin_cases r <;> assumption

end St

/-- Normalize register reads and writes of named register files. -/
syntax "regs" (" [" (Lean.Parser.Tactic.simpLemma),* "]")? (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| regs $[$loc:location]?) =>
    `(tactic| simp only [St.toV_n, St.toV_a, St.toV_X, St.toV_P, St.toV_T, St.toV_Z, St.toV_C,
      St.toV_s, St.toV_w, St.toV_K, St.toV_U, St.toV_V, St.toV_M, St.toV_I, St.toV_SE, St.toV_SP,
      St.toV_E, St.toV_Q, St.upd_n, St.upd_a, St.upd_X, St.upd_P, St.upd_T, St.upd_Z, St.upd_C,
      St.upd_s, St.upd_w, St.upd_K, St.upd_U, St.upd_V, St.upd_M, St.upd_I, St.upd_SE, St.upd_SP,
      St.upd_E, St.upd_Q] $[$loc]?)
  | `(tactic| regs [$args,*] $[$loc:location]?) =>
    `(tactic| simp only [St.toV_n, St.toV_a, St.toV_X, St.toV_P, St.toV_T, St.toV_Z, St.toV_C,
      St.toV_s, St.toV_w, St.toV_K, St.toV_U, St.toV_V, St.toV_M, St.toV_I, St.toV_SE, St.toV_SP,
      St.toV_E, St.toV_Q, St.upd_n, St.upd_a, St.upd_X, St.upd_P, St.upd_T, St.upd_Z, St.upd_C,
      St.upd_s, St.upd_w, St.upd_K, St.upd_U, St.upd_V, St.upd_M, St.upd_I, St.upd_SE, St.upd_SP,
      St.upd_E, St.upd_Q,
      $args,*] $[$loc]?)

/-! ## Labels -/

/-- The sites of the move loops (`src` is added to `dst` and cleared; see `mvSrc`, `mvDst`). -/
inductive MvS where
  /-- setup: `n` into `a` -/
  | aN
  /-- multiplication: the product `T` back into `P` (`f`: squaring, else a power step) -/
  | mulT (f : Bool)
  /-- setup: `P` into the width `w` -/
  | wP
  /-- push: the saved endpoint (`U` if `b`, else `V`) into `SE` -/
  | pushX (b : Bool)
  /-- push: the doubled phase stack `T` back into `SP` -/
  | pushSP (b : Bool)
  /-- descent: the midpoint `M` into `V` -/
  | descM
  /-- phase-`0` success: `V` into `U` -/
  | a0T1
  /-- phase-`0` success: the popped endpoint `E` into `V` -/
  | a0T2
  /-- pop: the last digit, left in `SE`, into `E` -/
  | popE (b : Bool)
  /-- pop: the remaining stack `T` back into `SE` -/
  | popT2 (b : Bool)
  /-- phase-`0` failure: `V` into `M` -/
  | a0FM
  /-- phase-`0` failure: the popped endpoint `E` into `V` -/
  | a0FV
  /-- phase-`1` success: the popped endpoint `E` into `U` -/
  | a1TU
  /-- phase-`1` failure: `U` into `M` -/
  | a1FM
  /-- phase-`1` failure: the popped endpoint `E` into `U` -/
  | a1FU
  deriving DecidableEq, Fintype

/-- The sites of the copy loops (`src` is added to `dst` through `Z`; see `cpSrc`, `cpDst`). -/
inductive CpS where
  /-- multiplication: the multiplier (`P` if `f`, else `a`) into the counter `C` -/
  | mulF (f : Bool)
  /-- multiplication: `P` into the accumulator `T` -/
  | mulP (f : Bool)
  /-- setup: `P` into the radius `s` -/
  | sP
  /-- setup: `w` into `C`, the shift count of `K := 2 ^ w` -/
  | kW
  /-- root: `w` into the level `I` -/
  | rootW
  /-- push: `w` into `C`, the shift count of `SE` -/
  | push (b : Bool)
  /-- pop: the stack `SE` into `T` -/
  | popS (b : Bool)
  /-- pop: `w` into `C`, the halving count of `T` -/
  | popW1 (b : Bool)
  /-- pop: the halved stack `T` into `Q` -/
  | popT (b : Bool)
  /-- pop: `w` into `C`, the shift count of `Q` -/
  | popW2 (b : Bool)
  deriving DecidableEq, Fintype

/-- The sites of the shift loops (`r := r · 2 ^ C`; see `shReg`). -/
inductive ShS where
  /-- setup: `K := K · 2 ^ w` -/
  | kK
  /-- push: `SE := SE · 2 ^ w`, making room for a digit -/
  | push (b : Bool)
  /-- pop: `Q := Q · 2 ^ w`, the stack without its last digit, shifted back -/
  | pop (b : Bool)
  deriving DecidableEq, Fintype

/-- **The labels of the Savitch machine**: the setup (`scan` … `kInit`), the outer search
(`OU` … `rej`), the recursion (`cl` … `a1Finc`), and the loop families `mv`, `dm`, `sb`, `hv`,
`cp`, `sh` (a site and a phase). -/
inductive Lb (E : ℕ) where
  /-- setup: query the input-length decider at `n` -/
  | scan
  /-- setup: increment `n` -/
  | incN
  /-- setup: first increment of `a` -/
  | incA1
  /-- setup: second increment of `a` -/
  | incA2
  /-- setup: the `j`-th increment of the exponent counter `X` (then `P := 1`) -/
  | ld (j : Fin (E + 1))
  /-- setup: test the exponent counter `X` -/
  | pw
  /-- setup: decrement `X` before a power step -/
  | pwDec
  /-- multiplication: test the counter `C` -/
  | mulL (f : Bool)
  /-- multiplication: decrement `C` -/
  | mulD (f : Bool)
  /-- multiplication: clear `P` before moving the product back -/
  | mulFin (f : Bool)
  /-- setup: clear `a` -/
  | clrA
  /-- setup: `K := 1` before the shift -/
  | kInit
  /-- outer search: test `U = K` -/
  | OU
  /-- outer search: query the initial-code decider at `U` -/
  | OUc
  /-- outer search: next `U` -/
  | NU
  /-- outer search: test `V = K` -/
  | OV
  /-- outer search: clear `V` at the end of the inner loop -/
  | OVend
  /-- outer search: query the accepting-code decider at `V` -/
  | OVc
  /-- outer search: next `V` -/
  | NV
  /-- root: clear the level `I` -/
  | root
  /-- root failure: clear `I` and try the next `V` -/
  | rootF
  /-- accept -/
  | acc
  /-- reject -/
  | rej
  /-- recursion: a call; test the level `I` -/
  | cl
  /-- level `0`: query the step decider at `(U, V)` -/
  | base
  /-- level `0`: test `U = V` -/
  | baseEq
  /-- recursion: clear the midpoint `M` -/
  | lInit
  /-- recursion: test `M = K` -/
  | loop
  /-- return with answer `b`: test whether the node is the root -/
  | rt (b : Bool)
  /-- return: restore the level `I` -/
  | incI (b : Bool)
  /-- return: test the parity of the phase stack `SP` -/
  | par (b : Bool)
  /-- return to a phase-`0` frame: pop the phase bit -/
  | h0 (b : Bool)
  /-- return to a phase-`1` frame: pop the phase bit -/
  | h1 (b : Bool)
  /-- descent: decrement `I` -/
  | descDec
  /-- push: set the new phase bit `1` -/
  | pushInc
  /-- phase-`0` success: decrement `I` and descend into `(M, V)` -/
  | a0Dec
  /-- phase-`0` failure: clear `M` -/
  | a0F
  /-- phase-`0` failure: next midpoint -/
  | a0Finc
  /-- phase-`1` success: clear `U` -/
  | a1T
  /-- phase-`1` failure: clear `M` -/
  | a1F
  /-- phase-`1` failure: next midpoint -/
  | a1Finc
  /-- a move loop at site `k`, phase `j` -/
  | mv (k : MvS) (j : Fin 3)
  /-- the doubling move `T += 2 · SP` of a push, phase `j` -/
  | dm (b : Bool) (j : Fin 4)
  /-- the subtraction `SE -= Q` of a pop, phase `j` -/
  | sb (b : Bool) (j : Fin 3)
  /-- the halving `T := T / 2 ^ C` of a pop, phase `j` -/
  | hv (b : Bool) (j : Fin 3)
  /-- a copy loop at site `k`, phase `j` -/
  | cp (k : CpS) (j : Fin 7)
  /-- a shift loop at site `k`, phase `j` -/
  | sh (k : ShS) (j : Fin 9)
  deriving DecidableEq, Fintype

variable {E : ℕ}

/-! ## Loop sites -/

/-- The source register of a move site. -/
def mvSrc : MvS → Fin 18
  | .aN => rn | .mulT _ => rT | .wP => rP | .pushX b => if b then rU else rV | .pushSP _ => rT
  | .descM => rM | .a0T1 => rV | .a0T2 => rE | .popE _ => rSE | .popT2 _ => rT | .a0FM => rV
  | .a0FV => rE | .a1TU => rE | .a1FM => rU | .a1FU => rE

/-- The target register of a move site. -/
def mvDst : MvS → Fin 18
  | .aN => ra | .mulT _ => rP | .wP => rw | .pushX _ => rSE | .pushSP _ => rSP
  | .descM => rV | .a0T1 => rU | .a0T2 => rV | .popE _ => rE | .popT2 _ => rSE | .a0FM => rM
  | .a0FV => rV | .a1TU => rU | .a1FM => rM | .a1FU => rU

/-- The exit label of a move site. -/
def mvExit : MvS → Lb E
  | .aN => .incA1 | .mulT f => if f then .mv .wP 0 else .pw | .wP => .clrA
  | .pushX b => .dm b 0 | .pushSP b => if b then .pushInc else .mv .descM 0
  | .descM => .descDec | .a0T1 => .mv .a0T2 0 | .a0T2 => .a0Dec | .popE b => .mv (.popT2 b) 0
  | .popT2 b => .incI b | .a0FM => .a0Finc | .a0FV => .loop | .a1TU => .rt true
  | .a1FM => .a1Finc | .a1FU => .loop

/-- The source register of a copy site. -/
def cpSrc : CpS → Fin 18
  | .mulF f => if f then rP else ra | .mulP _ => rP | .sP => rP | .kW => rw | .rootW => rw
  | .push _ => rw | .popS _ => rSE | .popW1 _ => rw | .popT _ => rT | .popW2 _ => rw

/-- The target register of a copy site. -/
def cpDst : CpS → Fin 18
  | .mulF _ => rC | .mulP _ => rT | .sP => rs | .kW => rC | .rootW => rI | .push _ => rC
  | .popS _ => rT | .popW1 _ => rC | .popT _ => rQ | .popW2 _ => rC

/-- The exit label of a copy site. -/
def cpExit : CpS → Lb E
  | .mulF f => .mulL f | .mulP f => .mulL f | .sP => .cp (.mulF true) 0 | .kW => .sh .kK 0
  | .rootW => .cl | .push b => .sh (.push b) 0 | .popS b => .cp (.popW1 b) 0
  | .popW1 b => .hv b 0 | .popT b => .cp (.popW2 b) 0 | .popW2 b => .sh (.pop b) 0

/-- The shifted register of a shift site. -/
def shReg : ShS → Fin 18
  | .kK => rK | .push _ => rSE | .pop _ => rQ

/-- The exit label of a shift site. -/
def shExit : ShS → Lb E
  | .kK => .OU | .push b => .mv (.pushX b) 0 | .pop b => .sb b 0

/-! ## The machine -/

/-- The move loop `jz src; dec src; inc dst`. -/
def mvI (src dst : Fin 18) (ex : Lb E) (mk : Fin 3 → Lb E) (j : Fin 3) : Ins 18 4 (Lb E) :=
  match j.val with
  | 0 => .jz src ex (mk 1)
  | 1 => .dec src (mk 2)
  | _ => .inc dst (mk 0)

/-- The doubled move loop `jz src; dec src; inc dst; inc dst`. -/
def dmI (src dst : Fin 18) (ex : Lb E) (mk : Fin 4 → Lb E) (j : Fin 4) : Ins 18 4 (Lb E) :=
  match j.val with
  | 0 => .jz src ex (mk 1)
  | 1 => .dec src (mk 2)
  | 2 => .inc dst (mk 3)
  | _ => .inc dst (mk 0)

/-- The subtraction loop `jz q; dec q; dec r`. -/
def sbI (q r : Fin 18) (ex : Lb E) (mk : Fin 3 → Lb E) (j : Fin 3) : Ins 18 4 (Lb E) :=
  match j.val with
  | 0 => .jz q ex (mk 1)
  | 1 => .dec q (mk 2)
  | _ => .dec r (mk 0)

/-- The halving loop `jz c; dec c; half r`. -/
def hvI (c r : Fin 18) (ex : Lb E) (mk : Fin 3 → Lb E) (j : Fin 3) : Ins 18 4 (Lb E) :=
  match j.val with
  | 0 => .jz c ex (mk 1)
  | 1 => .dec c (mk 2)
  | _ => .half r (mk 0)

/-- The copy loops through `Z`. -/
def cpI (src dst : Fin 18) (ex : Lb E) (mk : Fin 7 → Lb E) (j : Fin 7) : Ins 18 4 (Lb E) :=
  match j.val with
  | 0 => .jz src (mk 4) (mk 1)
  | 1 => .dec src (mk 2)
  | 2 => .inc dst (mk 3)
  | 3 => .inc rZ (mk 0)
  | 4 => .jz rZ ex (mk 5)
  | 5 => .dec rZ (mk 6)
  | _ => .inc src (mk 4)

/-- The shift loops: `r := r · 2 ^ C` through `Z`. -/
def shI (r : Fin 18) (ex : Lb E) (mk : Fin 9 → Lb E) (j : Fin 9) : Ins 18 4 (Lb E) :=
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

/-- **The Savitch machine** (constant `E`): deciders `0` (input length), `1` (initial
codes), `2` (accepting codes), `3` (step pairs).

* Setup: `n := |x|`; `a := n + 2`; `X := E`, `P := 1`; `E` times `P := P · a`; `s := P`;
  `P := P · P`; `w := P`; `K := 2 ^ w`.
* Outer search: for `U < K` with `U` initial, for `V < K` with `V` accepting, evaluate
  `Reach K R w U V` from level `I = w` (`root`); accept on success.
* Recursion (`cl`): at level `0` answer `U = V ∨ R U V`; above, run `M` through `0, …, K - 1`
  (`loop`), pushing `(V, 0)` and descending into `(U, M)`; on success pushing `(U, 1)` and
  descending into `(M, V)`. A finished node answers at `rt b`, which pops the parent's
  frame (`popS` … `popT2`), restores the level, and dispatches on the phase bit. -/
def A (E : ℕ) : ARM 18 4 (Lb E)
  | .scan => .call 0 .whole [rn] .incN (.mv .aN 0)
  | .incN => .inc rn .scan
  | .incA1 => .inc ra .incA2
  | .incA2 => .inc ra (.ld 0)
  | .ld j => if h : j.val < E then .inc rX (.ld ⟨j.val + 1, by omega⟩) else .inc rP .pw
  | .pw => .jz rX (.cp .sP 0) .pwDec
  | .pwDec => .dec rX (.cp (.mulF false) 0)
  | .mulL f => .jz rC (.mulFin f) (.mulD f)
  | .mulD f => .dec rC (.cp (.mulP f) 0)
  | .mulFin f => .clr rP (.mv (.mulT f) 0)
  | .clrA => .clr ra .kInit
  | .kInit => .inc rK (.cp .kW 0)
  | .OU => .jeq rU rK .rej .OUc
  | .OUc => .call 1 .whole [rU, rs] .OV .NU
  | .NU => .inc rU .OU
  | .OV => .jeq rV rK .OVend .OVc
  | .OVend => .clr rV .NU
  | .OVc => .call 2 .whole [rV, rs] .root .NV
  | .NV => .inc rV .OV
  | .root => .clr rI (.cp .rootW 0)
  | .rootF => .clr rI .NV
  | .acc => .ret true
  | .rej => .ret false
  | .cl => .jz rI .base .lInit
  | .base => .call 3 .whole [rU, rV, rs] (.rt true) .baseEq
  | .baseEq => .jeq rU rV (.rt true) (.rt false)
  | .lInit => .clr rM .loop
  | .loop => .jeq rM rK (.rt false) (.cp (.push false) 0)
  | .rt b => .jeq rI rw (if b then .acc else .rootF) (.cp (.popS b) 0)
  | .incI b => .inc rI (.par b)
  | .par b => .jodd rSP (.h1 b) (.h0 b)
  | .h0 b => .half rSP (if b then .cp (.push true) 0 else .a0F)
  | .h1 b => .half rSP (if b then .a1T else .a1F)
  | .descDec => .dec rI .cl
  | .pushInc => .inc rSP (.mv .a0T1 0)
  | .a0Dec => .dec rI .cl
  | .a0F => .clr rM (.mv .a0FM 0)
  | .a0Finc => .inc rM (.mv .a0FV 0)
  | .a1T => .clr rU (.mv .a1TU 0)
  | .a1F => .clr rM (.mv .a1FM 0)
  | .a1Finc => .inc rM (.mv .a1FU 0)
  | .mv k j => mvI (mvSrc k) (mvDst k) (mvExit k) (.mv k) j
  | .dm b j => dmI rSP rT (.mv (.pushSP b) 0) (.dm b) j
  | .sb b j => sbI rQ rSE (.mv (.popE b) 0) (.sb b) j
  | .hv b j => hvI rC rT (.cp (.popT b) 0) (.hv b) j
  | .cp k j => cpI (cpSrc k) (cpDst k) (cpExit k) (.cp k) j
  | .sh k j => shI (shReg k) (shExit k) (.sh k) j

end SavitchARM

end Complexity.LogProg
