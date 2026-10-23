/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyCode
import TCSlib.Complexity.SpaceComplexity.Machines.NARMPSem
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops
import TCSlib.Complexity.SpaceComplexity.Machines.VWord
import TCSlib.Complexity.SpaceComplexity.Codec.Engine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The repetition machine for error reduction in logarithmic space

[AB09, §7.7, p. 139]: "the error reduction procedure … can be implemented with only
logarithmic space overhead". The machine `Randomized.PolyAmp.ampA` is a probabilistic register
machine (`Complexity.LogProg.NARM`) that repeats a space-bounded PTM `N` polynomially often.
It keeps `N`'s configuration as a code (`Complexity.Codec.cfgCode`) in a register and asks
the logspace deciders of the code languages of `N`:

1. measure `n = |x|` and `ℓ = |bits n| + 1`, the radius `s = c_S ℓ` and `K = 2^{F ℓ}`;
2. `K + 1` times: find the initial code; `K` times read a coin and move to the least (coin
   `1`) or greatest (coin `0`) step partner of the current code; count the run if its last
   code is accepting;
3. answer by the majority of the runs (two-sided) or by "some run accepted" (one-sided).

The two step partners of a code are the codes of its two successors, so the coin picks each
successor with probability `1/2`. This file holds the machine and its register file; the
semantics is in `TCSlib.Complexity.Randomized.SpaceAmplifyPolyRun`.

## Main definitions

* `Randomized.PolyAmp.ampA` — the machine.
* `Randomized.PolyAmp.Reg` — its register file.

## Main results

* `Randomized.PolyAmp.ampA_npreS` — the machine meets the syntactic preconditions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.PolyAmp

open Complexity Complexity.LogProg Turing

/-! ## The machine -/

/-- The copy sites of the machine (`dst := dst + src` through the scratch register). -/
inductive CpS
  | nt | la1 | la2 | kR | ri | kj | kc | cc
  deriving DecidableEq, Fintype

/-- The source of a copy site. -/
def cpSrc : CpS → Fin 15
  | .nt => 0 | .la1 => 1 | .la2 => 1 | .kR => 4 | .ri => 5 | .kj => 4 | .kc => 4 | .cc => 9

/-- The destination of a copy site. -/
def cpDst : CpS → Fin 15
  | .nt => 12 | .la1 => 13 | .la2 => 13 | .kR => 5 | .ri => 6 | .kj => 10 | .kc => 9 | .cc => 8

/-- The labels of the repetition machine: input length (`len*`), copies (`cp* k`), the digit
count (`h*`), the two scalings (`s*0`, `s*1`), the power (`sh*`), the run loop (`rT`, `rD`),
the initial-code search (`i*`), the step loop (`sT`, `sD`, `coin`), the upward and downward
searches for a step partner (`u*`, `d*`), the move (`mv`), the acceptance check (`chk`,
`cI`), the final comparison (`fin`, `ad*`, `fC`, `lt*`) and the two answers. -/
inductive Lab (cS F : ℕ)
  | len | lenI
  | cp0 (k : CpS) | cp1 (k : CpS) | cp2 (k : CpS) | cp3 (k : CpS) | cp4 (k : CpS)
  | cp5 (k : CpS) | cp6 (k : CpS)
  | hT | hH | hB | lI
  | sT0 | sD0 | sI0 (i : Fin cS)
  | sT1 | sD1 | sI1 (i : Fin F)
  | kI | sh0 | sh1 | sh2 | sh3 | sh4 | sh5 | sh6 | sh7 | sh8 | rI
  | rT | rD | iC | iT | iI
  | sT | sD | coin | up | uT | uI | dn | dD | dT | mv | chk | cI
  | fin | ad1 | ad2 | ad3 | fC | lt1 | lt2 | ltb
  | acc | rej
  deriving DecidableEq, Fintype

variable {cS F : ℕ}

/-- The exit of a copy site. -/
def cpEx : CpS → Lab cS F
  | .nt => .hT | .la1 => .sT0 | .la2 => .sT1 | .kR => .rI | .ri => .rT | .kj => .sT
  | .kc => .dD | .cc => .sT

/-- The increment chain of the radius scaling: `sI0 i` for `i < c_S`, then back to the test. -/
def sL0 (i : ℕ) : Lab cS F := if h : i < cS then .sI0 ⟨i, h⟩ else .sT0

/-- The increment chain of the exponent scaling: `sI1 i` for `i < F`, then back to the test. -/
def sL1 (i : ℕ) : Lab cS F := if h : i < F then .sI1 ⟨i, h⟩ else .sT1

/-- **The repetition machine** [AB09, §7.7, p. 139]. Registers: `0` the input length `n`,
`1` `ℓ = |bits n| + 1`, `2` the radius `s = c_S ℓ`, `3` the exponent `F ℓ`, `4` `K = 2^{F ℓ}`,
`5` the number `K + 1` of runs, `6` the runs left, `7` the accepting runs, `8` the current
code, `9` a candidate code, `10` the coins left in the run, `11`, `12`, `13`, `14` scratch.
Deciders: `0` the input length, `1`, `2`, `3` the initial, step and accepting codes of `N`.
With `os` (one-sided) it accepts iff some run accepted; otherwise iff `2 · count > K + 1`. -/
def ampA (cS F : ℕ) (os : Bool) : NARM 15 4 (Lab cS F)
  | .len => .det (.call 0 .whole [0] .lenI (.cp0 .nt))
  | .lenI => .det (.inc 0 .len)
  | .cp0 k => .det (.jz (cpSrc k) (.cp4 k) (.cp1 k))
  | .cp1 k => .det (.dec (cpSrc k) (.cp2 k))
  | .cp2 k => .det (.inc (cpDst k) (.cp3 k))
  | .cp3 k => .det (.inc 11 (.cp0 k))
  | .cp4 k => .det (.jz 11 (cpEx k) (.cp5 k))
  | .cp5 k => .det (.dec 11 (.cp6 k))
  | .cp6 k => .det (.inc (cpSrc k) (.cp4 k))
  | .hT => .det (.jz 12 .lI .hH)
  | .hH => .det (.half 12 .hB)
  | .hB => .det (.inc 1 .hT)
  | .lI => .det (.inc 1 (.cp0 .la1))
  | .sT0 => .det (.jz 13 (.cp0 .la2) .sD0)
  | .sD0 => .det (.dec 13 (sL0 0))
  | .sI0 i => .det (.inc 2 (sL0 (i + 1)))
  | .sT1 => .det (.jz 13 .kI .sD1)
  | .sD1 => .det (.dec 13 (sL1 0))
  | .sI1 i => .det (.inc 3 (sL1 (i + 1)))
  | .kI => .det (.inc 4 .sh0)
  | .sh0 => .det (.jz 3 (.cp0 .kR) .sh1)
  | .sh1 => .det (.dec 3 .sh2)
  | .sh2 => .det (.jz 4 .sh6 .sh3)
  | .sh3 => .det (.dec 4 .sh4)
  | .sh4 => .det (.inc 11 .sh5)
  | .sh5 => .det (.inc 11 .sh2)
  | .sh6 => .det (.jz 11 .sh0 .sh7)
  | .sh7 => .det (.dec 11 .sh8)
  | .sh8 => .det (.inc 4 .sh6)
  | .rI => .det (.inc 5 (.cp0 .ri))
  | .rT => .det (.jz 6 .fin .rD)
  | .rD => .det (.dec 6 .iC)
  | .iC => .det (.clr 8 .iT)
  | .iT => .det (.call 1 .whole [8, 2] (.cp0 .kj) .iI)
  | .iI => .det (.inc 8 .iT)
  | .sT => .det (.jz 10 .chk .sD)
  | .sD => .det (.dec 10 .coin)
  | .coin => .choose .up .dn
  | .up => .det (.clr 9 .uT)
  | .uT => .det (.call 2 .whole [8, 9, 2] .mv .uI)
  | .uI => .det (.inc 9 .uT)
  | .dn => .det (.clr 9 (.cp0 .kc))
  | .dD => .det (.dec 9 .dT)
  | .dT => .det (.call 2 .whole [8, 9, 2] .mv .dD)
  | .mv => .det (.clr 8 (.cp0 .cc))
  | .chk => .det (.call 3 .whole [8, 2] .cI .rT)
  | .cI => .det (.inc 7 .rT)
  | .fin => if os then .det (.jz 7 .rej .acc) else .det (.jeq 12 7 .fC .ad1)
  | .ad1 => .det (.inc 14 .ad2)
  | .ad2 => .det (.inc 14 .ad3)
  | .ad3 => .det (.inc 12 .fin)
  | .fC => .det (.clr 12 .lt1)
  | .lt1 => .det (.jeq 12 14 .rej .lt2)
  | .lt2 => .det (.jeq 12 5 .acc .ltb)
  | .ltb => .det (.inc 12 .lt1)
  | .acc => .det (.ret true)
  | .rej => .det (.ret false)

/-- **The machine meets the syntactic preconditions**: its comparisons are of distinct
registers and its call arguments are distinct. -/
lemma ampA_npreS (os : Bool) (x : List Bool) (a : AConf 15 (Lab cS F)) :
    NPreS (ampA cS F os) x a := by
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · cases os <;> cases l <;> simp [NPreS, PreS, NARM.detPart, ampA]

/-- The deciders of the machine: input length, initial, step and accepting codes of `N`. -/
def ampAs (N : FinNDTM Bool) : Fin 4 → Language Bool :=
  ![inputLenLang, Codec.initLang N, Codec.stepLang N, Codec.acceptLang N]

/-- The deciders are logspace. -/
theorem ampAs_mem (N : FinNDTM Bool) (j : Fin 4) : ampAs N j ∈ LOGSPACE := by
  fin_cases j
  · exact inputLenLang_mem
  · exact Codec.initLang_mem (N := N)
  · exact Codec.stepLang_mem (N := N)
  · exact Codec.acceptLang_mem (N := N)

/-- The deciders' answers. -/
noncomputable abbrev ampOr (N : FinNDTM Bool) : Fin 4 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (ampAs N j : Set (List Bool)) V

/-! ## The register file -/

/-- The register file of the repetition machine, by name. -/
@[ext] structure Reg where
  /-- the input length (register `0`) -/
  n : ℕ
  /-- `ℓ` (register `1`) -/
  l : ℕ
  /-- the radius (register `2`) -/
  s : ℕ
  /-- the exponent (register `3`) -/
  e : ℕ
  /-- `K` (register `4`) -/
  K : ℕ
  /-- the number of runs (register `5`) -/
  R : ℕ
  /-- the runs left (register `6`) -/
  i : ℕ
  /-- the accepting runs (register `7`) -/
  cnt : ℕ
  /-- the current code (register `8`) -/
  c : ℕ
  /-- a candidate code (register `9`) -/
  d : ℕ
  /-- the coins left (register `10`) -/
  j : ℕ
  /-- scratch of the copies and the power (register `11`) -/
  z : ℕ
  /-- scratch of the digit count and the comparison (register `12`) -/
  t : ℕ
  /-- scratch of the scalings (register `13`) -/
  a : ℕ
  /-- twice the count (register `14`) -/
  w : ℕ

/-- The register values of a register file. -/
def Reg.v (σ : Reg) : Fin 15 → ℕ :=
  ![σ.n, σ.l, σ.s, σ.e, σ.K, σ.R, σ.i, σ.cnt, σ.c, σ.d, σ.j, σ.z, σ.t, σ.a, σ.w]

/-- Every register of a register file is at most `B`. -/
def Reg.Le (σ : Reg) (B : ℕ) : Prop :=
  σ.n ≤ B ∧ σ.l ≤ B ∧ σ.s ≤ B ∧ σ.e ≤ B ∧ σ.K ≤ B ∧ σ.R ≤ B ∧ σ.i ≤ B ∧ σ.cnt ≤ B ∧
    σ.c ≤ B ∧ σ.d ≤ B ∧ σ.j ≤ B ∧ σ.z ≤ B ∧ σ.t ≤ B ∧ σ.a ≤ B ∧ σ.w ≤ B

/-- The register-bound guard from the named bounds. -/
lemma Reg.le_v {σ : Reg} {B : ℕ} (h : σ.Le B) : ∀ r, σ.v r ≤ B := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  intro r
  fin_cases r <;> assumption

section RegSimp

variable (σ : Reg) (y : ℕ)

/-- Register `0` is `n`. -/
@[simp] lemma Reg.v_0 : σ.v 0 = σ.n := rfl
/-- Register `1` is `l`. -/
@[simp] lemma Reg.v_1 : σ.v 1 = σ.l := rfl
/-- Register `2` is `s`. -/
@[simp] lemma Reg.v_2 : σ.v 2 = σ.s := rfl
/-- Register `3` is `e`. -/
@[simp] lemma Reg.v_3 : σ.v 3 = σ.e := rfl
/-- Register `4` is `K`. -/
@[simp] lemma Reg.v_4 : σ.v 4 = σ.K := rfl
/-- Register `5` is `R`. -/
@[simp] lemma Reg.v_5 : σ.v 5 = σ.R := rfl
/-- Register `6` is `i`. -/
@[simp] lemma Reg.v_6 : σ.v 6 = σ.i := rfl
/-- Register `7` is `cnt`. -/
@[simp] lemma Reg.v_7 : σ.v 7 = σ.cnt := rfl
/-- Register `8` is `c`. -/
@[simp] lemma Reg.v_8 : σ.v 8 = σ.c := rfl
/-- Register `9` is `d`. -/
@[simp] lemma Reg.v_9 : σ.v 9 = σ.d := rfl
/-- Register `10` is `j`. -/
@[simp] lemma Reg.v_10 : σ.v 10 = σ.j := rfl
/-- Register `11` is `z`. -/
@[simp] lemma Reg.v_11 : σ.v 11 = σ.z := rfl
/-- Register `12` is `t`. -/
@[simp] lemma Reg.v_12 : σ.v 12 = σ.t := rfl
/-- Register `13` is `a`. -/
@[simp] lemma Reg.v_13 : σ.v 13 = σ.a := rfl
/-- Register `14` is `w`. -/
@[simp] lemma Reg.v_14 : σ.v 14 = σ.w := rfl
/-- Writing register `0` writes `n`. -/
@[simp] lemma Reg.u_0 : Function.update σ.v 0 y = { σ with n := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `1` writes `l`. -/
@[simp] lemma Reg.u_1 : Function.update σ.v 1 y = { σ with l := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `2` writes `s`. -/
@[simp] lemma Reg.u_2 : Function.update σ.v 2 y = { σ with s := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `3` writes `e`. -/
@[simp] lemma Reg.u_3 : Function.update σ.v 3 y = { σ with e := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `4` writes `K`. -/
@[simp] lemma Reg.u_4 : Function.update σ.v 4 y = { σ with K := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `5` writes `R`. -/
@[simp] lemma Reg.u_5 : Function.update σ.v 5 y = { σ with R := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `6` writes `i`. -/
@[simp] lemma Reg.u_6 : Function.update σ.v 6 y = { σ with i := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `7` writes `cnt`. -/
@[simp] lemma Reg.u_7 : Function.update σ.v 7 y = { σ with cnt := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `8` writes `c`. -/
@[simp] lemma Reg.u_8 : Function.update σ.v 8 y = { σ with c := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `9` writes `d`. -/
@[simp] lemma Reg.u_9 : Function.update σ.v 9 y = { σ with d := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `10` writes `j`. -/
@[simp] lemma Reg.u_10 : Function.update σ.v 10 y = { σ with j := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `11` writes `z`. -/
@[simp] lemma Reg.u_11 : Function.update σ.v 11 y = { σ with z := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `12` writes `t`. -/
@[simp] lemma Reg.u_12 : Function.update σ.v 12 y = { σ with t := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `13` writes `a`. -/
@[simp] lemma Reg.u_13 : Function.update σ.v 13 y = { σ with a := y }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `14` writes `w`. -/
@[simp] lemma Reg.u_14 : Function.update σ.v 14 y = { σ with w := y }.v := by
  funext r; fin_cases r <;> rfl

end RegSimp

/-- The probabilistic semantics of the repetition machine at label `l` with register file `σ`,
registers bounded by `B`. -/
abbrev PS (N : FinNDTM Bool) (os : Bool) (x : List Bool) (B : ℕ) (l : Lab cS F) (σ : Reg)
    (p : ℚ) : Prop :=
  PSem (ampA cS F os) (ampOr N) x (RegLe 15 (Lab cS F) B) (some l, σ.v, none) p

/-- Change the register file to an equal one. -/
lemma PS.of_eq {N : FinNDTM Bool} {os : Bool} {x : List Bool} {B : ℕ} {l : Lab cS F}
    {σ σ' : Reg} {p : ℚ} (h : σ = σ') (hp : PS N os x B l σ' p) : PS N os x B l σ p := h ▸ hp

end Randomized.PolyAmp
