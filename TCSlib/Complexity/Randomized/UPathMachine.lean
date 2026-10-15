/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.Randomized.UPath
import TCSlib.Complexity.SpaceComplexity.Machines.NARMPSem
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The random-walk machine for `UPATH`

[AB09, Theorem 7.19]: the machine `Complexity.LogProg.upA`, a nondeterministic abstract
register machine with fifteen registers whose `choose` bits are read as fair coins, calling
the input-access deciders `Complexity.LogProg.pathAs` of the `PATH` walk machine. It checks the
input deterministically — the unary prefix and the matrix shape as
`Complexity.LogProg.pathA` does, then the symmetry of the matrix, then it finds the source and
the target by comparing each candidate below `n` with their fields — computes `L = 100 n⁴`,
and walks from `s` for `L` steps, accepting as soon as it stands on `t`. A step reads
`size n` coins into an index `i < 2^{size n}` and moves to `i` if `i < n` and the edge bit is
`1`: the step `Randomized.padNbr` of the padded graph `Randomized.padGraph`.

Loops shared between several places are labelled by *sites*: copies
(`Complexity.LogProg.CpSite`), add-twice loops (`Complexity.LogProg.AdSite`), row-major index
computations (`Complexity.LogProg.IxSite`) and multiplications
(`Complexity.LogProg.MulSite`). This file defines the machine and its register file; the
proofs are in `TCSlib.Complexity.Randomized.UPathLoops`,
`TCSlib.Complexity.Randomized.UPathParse`, `TCSlib.Complexity.Randomized.UPathSearch`,
`TCSlib.Complexity.Randomized.UPathWalk` and `TCSlib.Complexity.Randomized.UPathRL`.

## Main definitions

* `Complexity.LogProg.ULabel`, `Complexity.LogProg.upA` — the machine.
* `Complexity.LogProg.UReg` — its register file, by name; `Complexity.LogProg.UPS` — the
  probabilistic semantics at a label and register file.

## Main results

* `Complexity.LogProg.upA_npreS` — the machine meets the syntactic preconditions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7, Theorem 7.19.)
-/

namespace Complexity.LogProg

open Turing

/-- The copy loops of the machine (`dst := src`, by counting up), named by their place. -/
inductive CpSite
  | yq | sTmp | sP | sCur | tQ | tTmp | tP | tT | wTmp | wNx | wCur
  deriving DecidableEq, Fintype

/-- The row-major index computations: two per symmetry test and one per walk step. -/
inductive IxSite
  | y0 | y1 | y2 | w
  deriving DecidableEq, Fintype

/-- The add-twice loops: three per index computation, five building `10 n`, one doubling
the random index. -/
inductive AdSite
  | ix (k : IxSite) (j : Fin 3)
  | ten (j : Fin 5)
  | dbl
  deriving DecidableEq, Fintype

/-- The two multiplications computing `100 n⁴ = (n · 10 n)²`. -/
inductive MulSite
  | m0 | m1
  deriving DecidableEq, Fintype

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The labels of the walk machine: the unary scan (`u*`) and matrix scan (`m*`) of
`Complexity.LogProg.pathA`, the symmetry test (`y*`), the source search (`s*`) and target
search (`t*`), the length computation (`lc`, `m*` sites), the walk (`w*`), the coin loop
(`c*`), the comparison `i < n` (`lt*`), the move (`wrd`, `mv`, `stay`), the shared loops by
site, and the two answers. -/
inductive ULabel
  | u0 | u1 | u2 | u3 | u4 | u5 | u6 | u7
  | m0 | mr | m1 | m2 | m3 | m4 | m5 | m7 | m8 | m9 | m10 | m11 | ms | m12
  | y0 | y1 | y2 | y4 | y6t | y6f | y7 | yn
  | s0 | s1 | s2 | s3 | s6
  | stt | sz1 | sz2 | sz3 | sz4 | sod | so1 | so2 | so3 | se1 | se2 | se3 | sad | shf
  | t0 | t1 | t2 | t3 | t4 | t6
  | ttt | tend | tlen | tpar | tone | tzero | tad | thf
  | lc (j : Fin 5)
  | mc (k : MulSite) | mo (k : MulSite) | mo1 (k : MulSite) | mi (k : MulSite)
  | mi1 (k : MulSite) | mi2 (k : MulSite) | mo2 (k : MulSite)
  | w0 | w1 | w2 | w3 | c0 | c1 | c2 | c3 | c4 | c5 | c6
  | lt | lt0 | lt1 | lt2 | wrd | mv | stay
  | cp (k : CpSite) | cpb (k : CpSite)
  | ad0 (k : AdSite) | ad1 (k : AdSite) | ad2 (k : AdSite) | ad3 (k : AdSite)
  | ix0 (k : IxSite) | ix1 (k : IxSite) | ix2 (k : IxSite) | ix3 (k : IxSite)
  | ix4 (k : IxSite) | ix5 (k : IxSite) | ix6 (k : IxSite) | ix7 (k : IxSite)
  | ix8 (k : IxSite)
  | acc | rej
  deriving DecidableEq, Fintype

open ULabel

/-- The destination of copy site `k`. -/
def cpDst : CpSite → Fin 15
  | .yq => 9 | .sTmp => 6 | .sP => 0 | .sCur => 4 | .tQ => 9 | .tTmp => 6 | .tP => 0
  | .tT => 5 | .wTmp => 6 | .wNx => 8 | .wCur => 4

/-- The source of copy site `k`. -/
def cpSrc : CpSite → Fin 15
  | .yq => 0 | .sTmp => 11 | .sP => 9 | .sCur => 11 | .tQ => 0 | .tTmp => 11 | .tP => 9
  | .tT => 11 | .wTmp => 1 | .wNx => 13 | .wCur => 8

/-- The exit of copy site `k`. -/
def cpEx : CpSite → ULabel
  | .yq => y0 | .sTmp => s3 | .sP => stt | .sCur => t0 | .tQ => t1 | .tTmp => t4 | .tP => ttt
  | .tT => lc 0 | .wTmp => c0 | .wNx => c4 | .wCur => stay

/-- The row register of index site `k`. -/
def ixRow : IxSite → Fin 15
  | .y0 => 11 | .y1 => 12 | .y2 => 12 | .w => 4

/-- The column register of index site `k`. -/
def ixCol : IxSite → Fin 15
  | .y0 => 12 | .y1 => 11 | .y2 => 11 | .w => 8

/-- The exit of index site `k`. -/
def ixEx : IxSite → ULabel
  | .y0 => y4 | .y1 => y6t | .y2 => y6f | .w => wrd

/-- The register added twice by add-twice site `k` (its counter is register `3`). -/
def adY : AdSite → Fin 15
  | .ix _ 0 => 1 | .ix _ 1 => 1 | .ix k 2 => ixCol k | .ten _ => 1 | .dbl => 8

/-- The register receiving the sum at add-twice site `k`. -/
def adP : AdSite → Fin 15
  | .ix _ _ => 0 | .ten _ => 13 | .dbl => 13

/-- The exit of add-twice site `k`. -/
def adEx : AdSite → ULabel
  | .ix k 0 => ix2 k | .ix k 1 => ix8 k | .ix k 2 => ixEx k
  | .ten j => ![lc 1, lc 2, lc 3, lc 4, mc .m0] j | .dbl => c3

/-- The outer bound of multiplication site `k` (its counters are registers `2` and `3`). -/
def mulA : MulSite → Fin 15 | .m0 => 1 | .m1 => 14

/-- The inner bound of multiplication site `k`. -/
def mulB : MulSite → Fin 15 | .m0 => 13 | .m1 => 14

/-- The result register of multiplication site `k`. -/
def mulR : MulSite → Fin 15 | .m0 => 14 | .m1 => 10

/-- The exit of multiplication site `k`. -/
def mulEx : MulSite → ULabel | .m0 => mc .m1 | .m1 => w0

/-- **The random-walk machine** [AB09, Theorem 7.19]. Registers: `0` the input pointer `p`,
`1` the vertex count `n`, `2`, `3` counters `a`, `b`, `4` the current vertex, `5` the target,
`6` a scratch copy, `7` the step count, `8` the random index, `9` a saved field position,
`10` the walk length `L`, `11`, `12` a row and column (the candidate vertex in the searches),
`13`, `14` scratch. Deciders: `0` reads an input bit, `1` compares with the input length.

* Unary and matrix scans as in `Complexity.LogProg.pathA`; save the source field position.
* Symmetry: for all `u, w < n`, read the bits at the matrix positions of `(u, w)` and
  `(w, u)`; reject if they differ.
* Source and target: for `c = 0, 1, …` below `n` compare `bits c` with the field (doubled,
  resp. plain and ending the input), restarting at the saved position; reject if none fits.
* Length: `e = 10 n` by five add-twice loops, `f = n · e`, `L = f · f`.
* Walk: accept if the current vertex is `t`, reject after `L` steps; otherwise `i := 0`, and
  for each of the `size n` halvings of a copy of `n`, `i := 2 i + coin`; if `i < n` and the
  matrix bit of `(cur, i)` is `1`, move to `i`; count the step. -/
def upA : NARM 15 2 ULabel
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
  | m12 => .det (.inc 0 (cp .yq))
  | y0 => .det (.jeq 11 1 s0 y1)
  | y1 => .det (.clr 12 y2)
  | y2 => .det (.jeq 12 1 yn (ix0 .y0))
  | y4 => .det (.call 0 .whole [0] (ix0 .y1) (ix0 .y2))
  | y6t => .det (.call 0 .whole [0] y7 rej)
  | y6f => .det (.call 0 .whole [0] rej y7)
  | y7 => .det (.inc 12 y2)
  | yn => .det (.inc 11 y0)
  | s0 => .det (.clr 11 s1)
  | s1 => .det (.jeq 11 1 rej s2)
  | s2 => .det (.clr 6 (cp .sTmp))
  | s3 => .det (.clr 0 (cp .sP))
  | stt => .det (.jz 6 sz1 sod)
  | sz1 => .det (.call 0 .whole [0] s6 sz2)
  | sz2 => .det (.inc 0 sz3)
  | sz3 => .det (.call 0 .whole [0] sz4 s6)
  | sz4 => .det (.inc 0 (cp .sCur))
  | sod => .det (.jodd 6 so1 se1)
  | so1 => .det (.call 0 .whole [0] so2 s6)
  | so2 => .det (.inc 0 so3)
  | so3 => .det (.call 0 .whole [0] sad s6)
  | se1 => .det (.call 0 .whole [0] s6 se2)
  | se2 => .det (.inc 0 se3)
  | se3 => .det (.call 0 .whole [0] s6 sad)
  | sad => .det (.inc 0 shf)
  | shf => .det (.half 6 stt)
  | s6 => .det (.inc 11 s1)
  | t0 => .det (.clr 9 (cp .tQ))
  | t1 => .det (.clr 11 t2)
  | t2 => .det (.jeq 11 1 rej t3)
  | t3 => .det (.clr 6 (cp .tTmp))
  | t4 => .det (.clr 0 (cp .tP))
  | ttt => .det (.jz 6 tend tlen)
  | tend => .det (.call 1 .whole [0] t6 (cp .tT))
  | tlen => .det (.call 1 .whole [0] tpar t6)
  | tpar => .det (.jodd 6 tone tzero)
  | tone => .det (.call 0 .whole [0] tad t6)
  | tzero => .det (.call 0 .whole [0] t6 tad)
  | tad => .det (.inc 0 thf)
  | thf => .det (.half 6 ttt)
  | t6 => .det (.inc 11 t2)
  | lc j => .det (.clr 3 (ad0 (.ten j)))
  | mc k => .det (.clr 2 (mo k))
  | mo k => .det (.jeq 2 (mulA k) (mulEx k) (mo1 k))
  | mo1 k => .det (.clr 3 (mi k))
  | mi k => .det (.jeq 3 (mulB k) (mo2 k) (mi1 k))
  | mi1 k => .det (.inc (mulR k) (mi2 k))
  | mi2 k => .det (.inc 3 (mi k))
  | mo2 k => .det (.inc 2 (mo k))
  | w0 => .det (.jeq 4 5 acc w1)
  | w1 => .det (.jeq 7 10 rej w2)
  | w2 => .det (.clr 8 w3)
  | w3 => .det (.clr 6 (cp .wTmp))
  | c0 => .det (.jz 6 lt c1)
  | c1 => .det (.clr 13 c2)
  | c2 => .det (.clr 3 (ad0 .dbl))
  | c3 => .det (.clr 8 (cp .wNx))
  | c4 => .choose c5 c6
  | c5 => .det (.inc 8 c6)
  | c6 => .det (.half 6 c0)
  | lt => .det (.clr 2 lt0)
  | lt0 => .det (.jeq 2 1 stay lt1)
  | lt1 => .det (.jeq 2 8 (ix0 .w) lt2)
  | lt2 => .det (.inc 2 lt0)
  | wrd => .det (.call 0 .whole [0] mv stay)
  | mv => .det (.clr 4 (cp .wCur))
  | stay => .det (.inc 7 w0)
  | cp k => .det (.jeq (cpDst k) (cpSrc k) (cpEx k) (cpb k))
  | cpb k => .det (.inc (cpDst k) (cp k))
  | ad0 k => .det (.jeq 3 (adY k) (adEx k) (ad1 k))
  | ad1 k => .det (.inc (adP k) (ad2 k))
  | ad2 k => .det (.inc (adP k) (ad3 k))
  | ad3 k => .det (.inc 3 (ad0 k))
  | ix0 k => .det (.clr 0 (ix1 k))
  | ix1 k => .det (.clr 3 (ad0 (.ix k 0)))
  | ix2 k => .det (.inc 0 (ix3 k))
  | ix3 k => .det (.inc 0 (ix4 k))
  | ix4 k => .det (.clr 2 (ix5 k))
  | ix5 k => .det (.jeq 2 (ixRow k) (ix7 k) (ix6 k))
  | ix6 k => .det (.clr 3 (ad0 (.ix k 1)))
  | ix8 k => .det (.inc 2 (ix5 k))
  | ix7 k => .det (.clr 3 (ad0 (.ix k 2)))
  | acc => .det (.ret true)
  | rej => .det (.ret false)

/-- **The machine meets the syntactic preconditions**: its comparisons are of distinct
registers and its calls have one argument. -/
lemma upA_npreS (x : List Bool) (a : AConf 15 ULabel) : NPreS upA x a := by
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · cases l <;> simp [NPreS, PreS, NARM.detPart, upA]
    all_goals first
      | (rename_i k; cases k <;> decide)
      | (rename_i k; cases k with
          | ix k j => cases k <;> fin_cases j <;> decide
          | ten j => fin_cases j <;> decide
          | dbl => decide)

/-- The register file of the walk machine, by name. -/
@[ext] structure UReg where
  /-- the input pointer (register `0`) -/
  p : ℕ
  /-- the vertex count (register `1`) -/
  n : ℕ
  /-- a row or outer counter (register `2`) -/
  a : ℕ
  /-- an inner counter (register `3`) -/
  b : ℕ
  /-- the current vertex (register `4`) -/
  cur : ℕ
  /-- the target (register `5`) -/
  t : ℕ
  /-- a scratch copy (register `6`) -/
  tmp : ℕ
  /-- the step count (register `7`) -/
  st : ℕ
  /-- the random index (register `8`) -/
  nx : ℕ
  /-- a saved field position (register `9`) -/
  q : ℕ
  /-- the walk length (register `10`) -/
  L : ℕ
  /-- a row or candidate vertex (register `11`) -/
  u : ℕ
  /-- a column (register `12`) -/
  w : ℕ
  /-- a scratch sum (register `13`) -/
  e : ℕ
  /-- a scratch product (register `14`) -/
  f : ℕ

/-- The register values of a register file. -/
def UReg.v (σ : UReg) : Fin 15 → ℕ :=
  ![σ.p, σ.n, σ.a, σ.b, σ.cur, σ.t, σ.tmp, σ.st, σ.nx, σ.q, σ.L, σ.u, σ.w, σ.e, σ.f]

/-- Every register of a register file is at most `B`. -/
def UReg.Le (σ : UReg) (B : ℕ) : Prop :=
  σ.p ≤ B ∧ σ.n ≤ B ∧ σ.a ≤ B ∧ σ.b ≤ B ∧ σ.cur ≤ B ∧ σ.t ≤ B ∧ σ.tmp ≤ B ∧ σ.st ≤ B ∧
    σ.nx ≤ B ∧ σ.q ≤ B ∧ σ.L ≤ B ∧ σ.u ≤ B ∧ σ.w ≤ B ∧ σ.e ≤ B ∧ σ.f ≤ B

/-- The register-bound guard from the named bounds. -/
lemma UReg.reg {σ : UReg} {B : ℕ} (h : σ.Le B) (l : Option ULabel) (res : Option Bool) :
    RegLe 15 ULabel B (l, σ.v, res) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  intro r
  fin_cases r <;> assumption

section URegSimp

variable (σ : UReg) (z : ℕ)

/-- Register `0` is the input pointer. -/
@[simp] lemma UReg.v_0 : σ.v 0 = σ.p := rfl
/-- Register `1` is the vertex count. -/
@[simp] lemma UReg.v_1 : σ.v 1 = σ.n := rfl
/-- Register `2` is a row or outer counter. -/
@[simp] lemma UReg.v_2 : σ.v 2 = σ.a := rfl
/-- Register `3` is an inner counter. -/
@[simp] lemma UReg.v_3 : σ.v 3 = σ.b := rfl
/-- Register `4` is the current vertex. -/
@[simp] lemma UReg.v_4 : σ.v 4 = σ.cur := rfl
/-- Register `5` is the target. -/
@[simp] lemma UReg.v_5 : σ.v 5 = σ.t := rfl
/-- Register `6` is a scratch copy. -/
@[simp] lemma UReg.v_6 : σ.v 6 = σ.tmp := rfl
/-- Register `7` is the step count. -/
@[simp] lemma UReg.v_7 : σ.v 7 = σ.st := rfl
/-- Register `8` is the random index. -/
@[simp] lemma UReg.v_8 : σ.v 8 = σ.nx := rfl
/-- Register `9` is a saved field position. -/
@[simp] lemma UReg.v_9 : σ.v 9 = σ.q := rfl
/-- Register `10` is the walk length. -/
@[simp] lemma UReg.v_10 : σ.v 10 = σ.L := rfl
/-- Register `11` is a row or candidate vertex. -/
@[simp] lemma UReg.v_11 : σ.v 11 = σ.u := rfl
/-- Register `12` is a column. -/
@[simp] lemma UReg.v_12 : σ.v 12 = σ.w := rfl
/-- Register `13` is a scratch sum. -/
@[simp] lemma UReg.v_13 : σ.v 13 = σ.e := rfl
/-- Register `14` is a scratch product. -/
@[simp] lemma UReg.v_14 : σ.v 14 = σ.f := rfl
/-- Writing register `0` writes the input pointer. -/
@[simp] lemma UReg.u_0 : Function.update σ.v 0 z = { σ with p := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `1` writes the vertex count. -/
@[simp] lemma UReg.u_1 : Function.update σ.v 1 z = { σ with n := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `2` writes a row or outer counter. -/
@[simp] lemma UReg.u_2 : Function.update σ.v 2 z = { σ with a := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `3` writes an inner counter. -/
@[simp] lemma UReg.u_3 : Function.update σ.v 3 z = { σ with b := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `4` writes the current vertex. -/
@[simp] lemma UReg.u_4 : Function.update σ.v 4 z = { σ with cur := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `5` writes the target. -/
@[simp] lemma UReg.u_5 : Function.update σ.v 5 z = { σ with t := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `6` writes a scratch copy. -/
@[simp] lemma UReg.u_6 : Function.update σ.v 6 z = { σ with tmp := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `7` writes the step count. -/
@[simp] lemma UReg.u_7 : Function.update σ.v 7 z = { σ with st := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `8` writes the random index. -/
@[simp] lemma UReg.u_8 : Function.update σ.v 8 z = { σ with nx := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `9` writes a saved field position. -/
@[simp] lemma UReg.u_9 : Function.update σ.v 9 z = { σ with q := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `10` writes the walk length. -/
@[simp] lemma UReg.u_10 : Function.update σ.v 10 z = { σ with L := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `11` writes a row or candidate vertex. -/
@[simp] lemma UReg.u_11 : Function.update σ.v 11 z = { σ with u := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `12` writes a column. -/
@[simp] lemma UReg.u_12 : Function.update σ.v 12 z = { σ with w := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `13` writes a scratch sum. -/
@[simp] lemma UReg.u_13 : Function.update σ.v 13 z = { σ with e := z }.v := by
  funext r; fin_cases r <;> rfl
/-- Writing register `14` writes a scratch product. -/
@[simp] lemma UReg.u_14 : Function.update σ.v 14 z = { σ with f := z }.v := by
  funext r; fin_cases r <;> rfl

end URegSimp

namespace UPathTac

/-- Normalize reads and updates of a named register file of the walk machine. -/
scoped macro "uw_regs" : tactic => `(tactic| simp only [UReg.v_0, UReg.v_1, UReg.v_2,
  UReg.v_3, UReg.v_4, UReg.v_5, UReg.v_6, UReg.v_7, UReg.v_8, UReg.v_9, UReg.v_10, UReg.v_11,
  UReg.v_12, UReg.v_13, UReg.v_14, UReg.u_0, UReg.u_1, UReg.u_2, UReg.u_3, UReg.u_4, UReg.u_5,
  UReg.u_6, UReg.u_7, UReg.u_8, UReg.u_9, UReg.u_10, UReg.u_11, UReg.u_12, UReg.u_13,
  UReg.u_14])
/-- Prove a register bound of the walk machine by linear arithmetic. -/
scoped macro "uw_le" : tactic => `(tactic| (simp only [UReg.Le] at *; omega))

/-- Prove an equality of register files field by field, simplifying first. -/
scoped macro "uw_ext" : tactic => `(tactic| (ext <;> (try simp) <;> (try omega)))

end UPathTac

open UPathTac

/-- The probabilistic semantics of the walk machine at label `l` with register file `σ`,
registers bounded by `B`. -/
abbrev UPS (x : List Bool) (B : ℕ) (l : ULabel) (σ : UReg) (p : ℚ) : Prop :=
  PSem upA pathOr x (RegLe 15 ULabel B) (some l, σ.v, none) p

/-- Change the register file to an equal one. -/
lemma UPS.of_eq {x : List Bool} {B : ℕ} {l : ULabel} {σ σ' : UReg} {p : ℚ} (h : σ = σ')
    (hp : UPS x B l σ' p) : UPS x B l σ p := h ▸ hp

end Complexity.LogProg
