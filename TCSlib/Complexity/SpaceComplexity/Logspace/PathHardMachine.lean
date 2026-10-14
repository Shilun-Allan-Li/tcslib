/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRegs
import TCSlib.Complexity.SpaceComplexity.Codec.Engine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The query register machine of the `PATH` reduction

The abstract register machine `Complexity.PathHard.A` answering the bit queries (`mode =
false`) and the length queries (`mode = true`) of the reduction `Complexity.PathHard.red`
[AB09, Theorem 4.18]: on a query `y = ⟨x, bits i⟩` it

1. measures `|y|` and scans the aligned pair `⟨x, β⟩` (rejecting non-pairs), so that the
   pointer `P = 2|x| + 2` marks the start of `β`, and recovers `|x|`;
2. computes `ℓ = |bits (|x| + 1)|`, the radius `S = a ℓ`, the exponent `E = b ℓ + f`, and
   `N = 2n`, `M = 2n²`, `K = 4n²` for `n = 2 ^ E` (with `a = c₀`, `b = K (c₀ + 1)`,
   `f = K + 2`, `K = codeK N` for the decider `N`);
3. checks that `β` is a canonical binary word of at most `|bits K|` letters (else `i` is out
   of range, or `y` is no query) and decodes `i`;
4. walks the layout of `red x`: the unary block, the separator, the doubled adjacency word —
   where the index of the matrix letter is split into a source `u` and a target `v` by
   halving and shifting by `E`, and the edge bit is asked from the initial-, accepting- or
   step-code decider (through `Complexity.dropIdx`, which removes `bits i` from the virtual
   input) — and the tail.

This file holds the machine and the run lemmas of its loop sites (instances of the generic loops of
`TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops`,
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess` and
`TCSlib.Complexity.SpaceComplexity.Codec.Engine`); its register file
`Complexity.PathHard.St` and its deciders `Complexity.PathHard.As` are in
`TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRegs`, the phases in
`TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRun`. A hand-written abstract register
machine: the walk is a fixed-layout dispatch with no reusable host behind it.

Infrastructure for [AB09, §4.3, Theorem 4.18]; not itself a result of the book.

## Main definitions

* `Complexity.PathHard.Lb`, `Complexity.PathHard.A` — the labels and the machine.
* `Complexity.PathHard.CpS`, `ShS`, `SbS`, `LeS` — the sites of the generic loops.

## Main results

* `Complexity.PathHard.preS_A` — the machine meets the syntactic preconditions.
* `Complexity.PathHard.cp_run`, `sh_run`, `sb_run`, `le_run` — the loop sites.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Theorem 4.18.)
-/

namespace Complexity.PathHard

open Turing LogProg

/-! ## Labels -/

/-- The sites of the copy loops `dst := src` (with `dst ≤ src`; see `cpDst`, `cpSrc`). -/
inductive CpS where
  /-- `x := p` -/
  | X
  /-- `t := x` -/
  | T
  /-- `t := c` -/
  | TC
  /-- `c := e`, before `2n := 2 ^ (e + 1)` -/
  | CN
  /-- `m := n` -/
  | MN
  /-- `c := e`, before `m := m · 2 ^ e` -/
  | CM
  /-- `k := m` -/
  | KM
  /-- `q := p` -/
  | QP
  /-- `u := i` -/
  | UI
  /-- `c := e`, before `u := u / 2 ^ e` -/
  | CU
  /-- `t := u` -/
  | TU
  /-- `c := e`, before `t := t · 2 ^ e` -/
  | CT
  deriving DecidableEq, Fintype

/-- The sites of the shift loops `r := r · 2 ^ c`. -/
inductive ShS where
  /-- `n := n · 2 ^ c`, giving `2n = 2 ^ (e + 1)` -/
  | N
  /-- `m := m · 2 ^ c`, giving `2n² = 2 ^ (2e + 1)` -/
  | M
  /-- `k := k · 2 ^ c`, giving the width cap `4n²` -/
  | K
  /-- `t := t · 2 ^ c`, shifting the source `u` of a matrix letter by `e` -/
  | T
  deriving DecidableEq, Fintype

/-- The sites of the subtraction loops `i := i - q`. -/
inductive SbS where
  /-- `i := i - n`, past the unary block `1²ⁿ` -/
  | N
  /-- `i := i - m`, past the doubled adjacency word -/
  | M
  /-- `i := i - t`, leaving the target `v` of a matrix letter -/
  | T
  deriving DecidableEq, Fintype

/-- The sites of the comparisons `a ≤ i` (with `a = n` or `a = m`). -/
inductive LeS where
  /-- `2n ≤ i`: past the unary block -/
  | N
  /-- `2n² ≤ i`: past the doubled adjacency word -/
  | M
  deriving DecidableEq, Fintype

set_option synthInstance.maxSize 4000 in
/-- **The labels of the query machine** (scale factors `a`, `b`, offset `f`). -/
inductive Lb (a b f : ℕ) where
  /-- measure: query the input length at `y` -/
  | lenQ
  /-- measure: increment `y` -/
  | lenI
  /-- pair scan: end test before a first letter -/
  | scan
  /-- pair scan: read the first letter of a pair -/
  | first
  /-- pair scan: end test before a second letter -/
  | test (b : Bool)
  /-- pair scan: read the second letter -/
  | read (b : Bool)
  /-- pair scan: advance the pointer (choice `k`) -/
  | adv (k : Fin 4)
  /-- `|x|`: first decrement of `x` -/
  | x1
  /-- `|x|`: second decrement of `x` -/
  | x2
  /-- `|x|`: halve `x` -/
  | x3
  /-- `t := x + 1` -/
  | t1
  /-- bit count: test `t` -/
  | hcT
  /-- bit count: halve `t` -/
  | hcH
  /-- bit count: increment `c` -/
  | hcB
  /-- radius: test `t` -/
  | sS
  /-- radius: decrement `t` -/
  | sSD
  /-- radius: increment `s` (`j`-th of `a`) -/
  | sSI (j : Fin a)
  /-- exponent: test `c` -/
  | sE
  /-- exponent: decrement `c` -/
  | sED
  /-- exponent: increment `e` (`j`-th of `b`) -/
  | sEI (j : Fin b)
  /-- exponent: the offset increments of `e` -/
  | eI (j : Fin f)
  /-- `c := e + 1` -/
  | n1
  /-- `n := 1` -/
  | n2
  /-- `c := 1` -/
  | k1
  /-- width check: end test (remembered last letter `b`) -/
  | tt (b : Bool)
  /-- width check: test the cap -/
  | tc
  /-- width check: read a letter -/
  | tr
  /-- width check: halve the cap -/
  | th (b : Bool)
  /-- width check: advance the pointer -/
  | tI (b : Bool)
  /-- decode: end test -/
  | dT
  /-- decode: decrement the pointer -/
  | dD
  /-- decode: read a letter -/
  | dR
  /-- decode: copy the accumulator into `d` -/
  | dC (b : Bool)
  /-- decode: increment `d` -/
  | dB (b : Bool)
  /-- decode: clear the accumulator -/
  | dL (b : Bool)
  /-- decode: test `d` -/
  | dS (b : Bool)
  /-- decode: decrement `d` -/
  | dK (b : Bool)
  /-- decode: increment the accumulator twice -/
  | dI (b : Bool) (j : Fin 2)
  /-- decode: add the letter -/
  | dA (b : Bool)
  /-- walk: clear `d` after `2n ≤ i` -/
  | wNy
  /-- walk: the separator, first letter -/
  | w2a
  /-- walk: decrement -/
  | w2b
  /-- walk: the separator, second letter -/
  | w2c
  /-- walk: decrement -/
  | w2d
  /-- walk: clear `d` after `2n² ≤ i` -/
  | wMy
  /-- tail: test position `j` -/
  | tl (j : Fin 5)
  /-- tail: decrement -/
  | td (j : Fin 4)
  /-- matrix: clear `d` -/
  | mx
  /-- matrix: halve the offset (or answer, in length mode) -/
  | mh
  /-- dispatch: test `u = 0` -/
  | dU
  /-- dispatch: decrement `u` -/
  | dU1
  /-- dispatch: test `u = 1` -/
  | dU2
  /-- dispatch: decrement `u` -/
  | dU3
  /-- source `0`: test `v = 0` -/
  | u0
  /-- source `0`: decrement -/
  | u0a
  /-- source `0`: test `v = 1` -/
  | u0b
  /-- source `0`: decrement -/
  | u0c
  /-- source `0`: ask the initial-code decider -/
  | u0d
  /-- source `≥ 2`: test `v = 0` -/
  | u2
  /-- source `≥ 2`: decrement -/
  | u2a
  /-- source `≥ 2`: test `v = 1` -/
  | u2b
  /-- source `≥ 2`, target `1`: ask the accepting-code decider -/
  | u2c
  /-- source `≥ 2`: decrement -/
  | u2d
  /-- source `≥ 2`, target `≥ 2`: ask the step decider -/
  | u2e
  /-- answer -/
  | ans (b : Bool)
  /-- a copy site -/
  | cp (k : CpS)
  /-- a copy site, increment -/
  | cpB (k : CpS)
  /-- a shift site, phase `j` -/
  | sh (k : ShS) (j : Fin 9)
  /-- a subtraction site, phase `j` -/
  | sb (k : SbS) (j : Fin 3)
  /-- a comparison site, phase `j` -/
  | le (k : LeS) (j : Fin 3)
  /-- the halving `u := u / 2 ^ c`, phase `j` -/
  | hv (j : Fin 3)
  deriving DecidableEq, Fintype

variable {a b f : ℕ}

/-! ## Sites -/

/-- The target of a copy site. -/
def cpDst : CpS → Fin 15
  | .X => rX | .T => rT | .TC => rT | .CN => rC | .MN => rM | .CM => rC | .KM => rK | .QP => rQ
  | .UI => rU | .CU => rC | .TU => rT | .CT => rC

/-- The source of a copy site. -/
def cpSrc : CpS → Fin 15
  | .X => rP | .T => rX | .TC => rC | .CN => rE | .MN => rN | .CM => rE | .KM => rM | .QP => rP
  | .UI => rI | .CU => rE | .TU => rU | .CT => rE

/-- The exit of a copy site. -/
def cpNext : CpS → Lb a b f
  | .X => .x1 | .T => .t1 | .TC => .sS | .CN => .n1 | .MN => .cp .CM | .CM => .sh .M 0
  | .KM => .k1 | .QP => .tt true | .UI => .cp .CU | .CU => .hv 0 | .TU => .cp .CT
  | .CT => .sh .T 0

/-- The shifted register of a shift site. -/
def shReg : ShS → Fin 15
  | .N => rN | .M => rM | .K => rK | .T => rT

/-- The exit of a shift site. -/
def shExit : ShS → Lb a b f
  | .N => .cp .MN | .M => .cp .KM | .K => .cp .QP | .T => .sb .T 0

/-- The subtracted register of a subtraction site. -/
def sbReg : SbS → Fin 15
  | .N => rN | .M => rM | .T => rT

/-- The exit of a subtraction site. -/
def sbExit : SbS → Lb a b f
  | .N => .w2a | .M => .tl 0 | .T => .dU

/-- The compared register of a comparison site. -/
def leReg : LeS → Fin 15
  | .N => rN | .M => rM

/-- The exit of a comparison site when `a ≤ i`. -/
def leYes : LeS → Lb a b f
  | .N => .wNy | .M => .wMy

/-- The exit of a comparison site when `i < a`. -/
def leNo : LeS → Lb a b f
  | .N => .ans true | .M => .mx

/-- The targets of the pair-scan advances. -/
def advT : Fin 4 → Lb a b f
  | 0 => .test false | 1 => .test true | 2 => .scan | 3 => .cp .X

/-- The pair-scan advance chains (stride `1`). -/
def advF (k : Fin 4) (i : ℕ) : Lb a b f := if i = 0 then .adv k else advT k

/-- The radius increment chain. -/
def sSinc (i : ℕ) : Lb a b f := if h : i < a then .sSI ⟨i, h⟩ else .sS

/-- The exponent increment chain. -/
def sEinc (i : ℕ) : Lb a b f := if h : i < b then .sEI ⟨i, h⟩ else .sE

/-- The exponent offset chain. -/
def eInc (i : ℕ) : Lb a b f := if h : i < f then .eI ⟨i, h⟩ else .cp .CN

/-- The width-check advance chains (stride `1`). -/
def tAdv (c : Bool) (i : ℕ) : Lb a b f := if i = 0 then .tI c else .tt c

/-- The decoding double-increment chains. -/
def dInc (c : Bool) (i : ℕ) : Lb a b f := if h : i < 2 then .dI c ⟨i, h⟩ else .dS c

/-- The tail answers: the tail of the layout is `0 1 0 1 1`; in length mode every tail
position is inside. -/
def tailAns (mode : Bool) (j : Fin 5) : Bool := if j.val = 1 ∨ 3 ≤ j.val then true else mode

/-- The copy loop `jeq dst src next bump; bump: inc dst`. -/
def cpI (k : CpS) (bump : Bool) : Ins 15 5 (Lb a b f) :=
  if bump then .inc (cpDst k) (.cp k) else .jeq (cpDst k) (cpSrc k) (cpNext k) (.cpB k)

/-- The shift loops `r := r · 2 ^ c` through `z`. -/
def shI (r : Fin 15) (ex : Lb a b f) (mk : Fin 9 → Lb a b f) (j : Fin 9) : Ins 15 5 (Lb a b f) :=
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

/-- The subtraction loop `jz q; dec q; dec i`. -/
def sbI (q : Fin 15) (ex : Lb a b f) (mk : Fin 3 → Lb a b f) (j : Fin 3) : Ins 15 5 (Lb a b f) :=
  match j.val with
  | 0 => .jz q ex (mk 1)
  | 1 => .dec q (mk 2)
  | _ => .dec rI (mk 0)

/-- The comparison loop `jeq d a yes; jeq d i no; inc d`. -/
def leI (r : Fin 15) (yes no : Lb a b f) (mk : Fin 3 → Lb a b f) (j : Fin 3) :
    Ins 15 5 (Lb a b f) :=
  match j.val with
  | 0 => .jeq rD r yes (mk 1)
  | 1 => .jeq rD rI no (mk 2)
  | _ => .inc rD (mk 0)

/-- The halving loop `jz c; dec c; half u`. -/
def hvI (j : Fin 3) : Ins 15 5 (Lb a b f) :=
  match j.val with
  | 0 => .jz rC (.cp .TU) (.hv 1)
  | 1 => .dec rC (.hv 2)
  | _ => .half rU (.hv 0)

/-- **The query machine** (bit queries if `mode = false`, length queries if `mode = true`),
with deciders `0` (input bits), `1` (input length), `2`, `3`, `4` (initial, accepting and
step codes, through `dropIdx`). See the module docstring for the phases. -/
def A (a b f : ℕ) (mode : Bool) : ARM 15 5 (Lb a b f)
  | .lenQ => .call 1 .whole [rY] .lenI .scan
  | .lenI => .inc rY .lenQ
  | .scan => .jeq rP rY (.ans false) .first
  | .first => .call 0 .whole [rP] (advF 1 0) (advF 0 0)
  | .test c => .jeq rP rY (.ans false) (.read c)
  | .read c => .call 0 .whole [rP] (if c then advF 2 0 else advF 3 0)
      (if c then .ans false else advF 2 0)
  | .adv k => .inc rP (advF k 1)
  | .x1 => .dec rX .x2
  | .x2 => .dec rX .x3
  | .x3 => .half rX (.cp .T)
  | .t1 => .inc rT .hcT
  | .hcT => .jz rT (.cp .TC) .hcH
  | .hcH => .half rT .hcB
  | .hcB => .inc rC .hcT
  | .sS => .jz rT .sE .sSD
  | .sSD => .dec rT (sSinc 0)
  | .sSI j => .inc rS (sSinc (j.val + 1))
  | .sE => .jz rC (eInc 0) .sED
  | .sED => .dec rC (sEinc 0)
  | .sEI j => .inc rE (sEinc (j.val + 1))
  | .eI j => .inc rE (eInc (j.val + 1))
  | .n1 => .inc rC .n2
  | .n2 => .inc rN (.sh .N 0)
  | .k1 => .inc rC (.sh .K 0)
  | .tt c => .jeq rQ rY (if c then .dT else .ans false) .tc
  | .tc => .jz rK (.ans false) .tr
  | .tr => .call 0 .whole [rQ] (.th true) (.th false)
  | .th c => .half rK (tAdv c 0)
  | .tI c => .inc rQ (tAdv c 1)
  | .dT => .jeq rY rP (.le .N 0) .dD
  | .dD => .dec rY .dR
  | .dR => .call 0 .whole [rY] (.dC true) (.dC false)
  | .dC c => .jeq rD rI (.dL c) (.dB c)
  | .dB c => .inc rD (.dC c)
  | .dL c => .clr rI (.dS c)
  | .dS c => .jz rD (.dA c) (.dK c)
  | .dK c => .dec rD (dInc c 0)
  | .dI c j => .inc rI (dInc c (j.val + 1))
  | .dA c => if c then .inc rI .dT else .jz rD .dT .dT
  | .wNy => .clr rD (.sb .N 0)
  | .w2a => .jz rI (.ans mode) .w2b
  | .w2b => .dec rI .w2c
  | .w2c => .jz rI (.ans true) .w2d
  | .w2d => .dec rI (.le .M 0)
  | .wMy => .clr rD (.sb .M 0)
  | .tl j => .jz rI (.ans (tailAns mode j)) (if h : j.val < 4 then .td ⟨j.val, h⟩ else .ans false)
  | .td j => .dec rI (.tl j.succ)
  | .mx => .clr rD .mh
  | .mh => if mode then .ret true else .half rI (.cp .UI)
  | .dU => .jz rU .u0 .dU1
  | .dU1 => .dec rU .dU2
  | .dU2 => .jz rU (.ans false) .dU3
  | .dU3 => .dec rU .u2
  | .u0 => .jz rI (.ans false) .u0a
  | .u0a => .dec rI .u0b
  | .u0b => .jz rI (.ans false) .u0c
  | .u0c => .dec rI .u0d
  | .u0d => .call 2 .whole [rI, rS] (.ans true) (.ans false)
  | .u2 => .jz rI (.ans false) .u2a
  | .u2a => .dec rI .u2b
  | .u2b => .jz rI .u2c .u2d
  | .u2c => .call 3 .whole [rU, rS] (.ans true) (.ans false)
  | .u2d => .dec rI .u2e
  | .u2e => .call 4 .whole [rU, rI, rS] (.ans true) (.ans false)
  | .ans c => .ret c
  | .cp k => cpI k false
  | .cpB k => cpI k true
  | .sh k j => shI (shReg k) (shExit k) (.sh k) j
  | .sb k j => sbI (sbReg k) (sbExit k) (.sb k) j
  | .le k j => leI (leReg k) (leYes k) (leNo k) (.le k) j
  | .hv j => hvI j

/-! ## Preconditions and run helpers -/

variable (mode : Bool) (o : Fin 5 → List Bool → Bool) (y : List Bool) (B : ℕ)

/-- **The query machine meets the syntactic preconditions** everywhere: its equality tests
compare distinct registers and its calls have distinct arguments. -/
lemma preS_A (c : AConf 15 (Lb a b f)) : PreS (A a b f mode) y c := by
  rcases c with ⟨_ | l, v, res⟩
  · trivial
  · cases l with
    | cp k => cases k <;> simp [PreS, A, cpI, cpDst, cpSrc] <;> decide
    | cpB k => simp [PreS, A, cpI]
    | sh k j => fin_cases j <;> simp [PreS, A, shI]
    | sb k j => fin_cases j <;> simp [PreS, A, sbI]
    | le k j => cases k <;> fin_cases j <;> simp [PreS, A, leI, leReg] <;> decide
    | hv j => fin_cases j <;> simp [PreS, A, hvI]
    | tl j => simp [PreS, A]
    | mh => cases mode <;> simp [PreS, A]
    | dA c => cases c <;> simp [PreS, A]
    | _ => simp [PreS, A] <;> decide

variable {mode o y B}

/-- A bounded register file at a label meets the guard. -/
lemma gb_of {st : St} (hbd : st.Bd B) (l : Lb a b f) :
    GuardLe (A a b f mode) y B (some l, st.toV, none) := ⟨preS_A mode y _, hbd.toV⟩

/-- One step from a bounded register file. -/
lemma step_of {st : St} {l : Lb a b f} {c : AConf 15 (Lb a b f)} (hbd : st.Bd B)
    (h : AReach (A a b f mode) o y (GuardLe (A a b f mode) y B)
      (astep (A a b f mode) o y (some l, st.toV, none)) c) :
    AReach (A a b f mode) o y (GuardLe (A a b f mode) y B) (some l, st.toV, none) c :=
  AReach.step (gb_of hbd l) h

/-- One step from a bounded register file, then a halting run. -/
lemma stepH_of {st : St} {l : Lb a b f} {r : Bool} (hbd : st.Bd B)
    (h : AHalt (A a b f mode) o y (GuardLe (A a b f mode) y B)
      (astep (A a b f mode) o y (some l, st.toV, none)) r) :
    AHalt (A a b f mode) o y (GuardLe (A a b f mode) y B) (some l, st.toV, none) r :=
  AHalt.step (gb_of hbd l) h

/-- Answering from a bounded register file. -/
lemma ans_halt {st : St} (hbd : st.Bd B) (r : Bool) :
    AHalt (A a b f mode) o y (GuardLe (A a b f mode) y B) (some (.ans r), st.toV, none) r :=
  AHalt.ret rfl (gb_of hbd _)

/-- Continue a run from an equal register file. -/
lemma cont {st st' : St} {l : Lb a b f} {c : AConf 15 (Lb a b f)} (e : st = st')
    (h : AReach (A a b f mode) o y (GuardLe (A a b f mode) y B) (some l, st'.toV, none) c) :
    AReach (A a b f mode) o y (GuardLe (A a b f mode) y B) (some l, st.toV, none) c := e ▸ h

/-- Continue a halting run from an equal register file. -/
lemma contH {st st' : St} {l : Lb a b f} {r : Bool} (e : st = st')
    (h : AHalt (A a b f mode) o y (GuardLe (A a b f mode) y B) (some l, st'.toV, none) r) :
    AHalt (A a b f mode) o y (GuardLe (A a b f mode) y B) (some l, st.toV, none) r := e ▸ h

/-! ## Loop sites -/

/-- Copy sites copy between distinct registers. -/
lemma cp_ne (k : CpS) : cpDst k ≠ cpSrc k := by cases k <;> decide

/-- **A copy site** sets its target to its source (from a smaller target). -/
theorem cp_run (k : CpS) (st : St) (hbd : st.Bd B) (hle : st.toV (cpDst k) ≤ st.toV (cpSrc k)) :
    AReach (A a b f mode) o y (GuardLe (A a b f mode) y B) (some (.cp k), st.toV, none)
      (some (cpNext k), Function.update st.toV (cpDst k) (st.toV (cpSrc k)), none) :=
  registerCopy_loop (A a b f mode) o y (cpDst k) (cpSrc k) (cp_ne k) (.cp k) (.cpB k)
    (cpNext k) rfl rfl B st.toV hbd.toV hle

/-- Shift sites have distinct registers. -/
lemma sh_ne (k : ShS) : rC ≠ shReg k ∧ rC ≠ rZ ∧ shReg k ≠ rZ := by cases k <;> decide

/-- **A shift site** multiplies its register by `2 ^ c` and clears `c`. -/
theorem sh_run (k : ShS) (st : St) (hbd : st.Bd B) (hZ : st.z = 0)
    (hb : st.toV (shReg k) * 2 ^ st.c ≤ B) :
    AReach (A a b f mode) o y (GuardLe (A a b f mode) y B) (some (.sh k 0), st.toV, none)
      (some (shExit k), Function.update (Function.update st.toV rC 0) (shReg k)
        (st.toV (shReg k) * 2 ^ st.c), none) :=
  shl_run (A := A a b f mode) (oracle := o) (x := y) (B := B) (l := .sh k 0) (l1 := .sh k 1)
    (l2 := .sh k 2) (l3 := .sh k 3) (l4 := .sh k 4) (l5 := .sh k 5) (l6 := .sh k 6)
    (l7 := .sh k 7) (l8 := .sh k 8) (lx := shExit k)
    (sh_ne k).1 (sh_ne k).2.1 (sh_ne k).2.2 rfl rfl rfl rfl rfl rfl rfl rfl rfl _ _ rfl
    hZ hbd.toV hb

/-- Subtraction sites subtract a register other than `i`. -/
lemma sb_ne (k : SbS) : sbReg k ≠ rI := by cases k <;> decide

/-- **A subtraction site** subtracts its register from `i` and clears it. -/
theorem sb_run (k : SbS) (st : St) (hbd : st.Bd B) :
    AReach (A a b f mode) o y (GuardLe (A a b f mode) y B) (some (.sb k 0), st.toV, none)
      (some (sbExit k), Function.update (Function.update st.toV (sbReg k) 0) rI
        (st.i - st.toV (sbReg k)), none) :=
  sub_run (A := A a b f mode) (oracle := o) (x := y) (B := B) (q := sbReg k) (r := rI)
    (l := .sb k 0) (l1 := .sb k 1) (l2 := .sb k 2) (lx := sbExit k)
    (sb_ne k) rfl rfl rfl _ st.toV rfl hbd.toV

/-- Comparison sites compare registers other than `d`. -/
lemma le_ne (k : LeS) : rD ≠ leReg k := by cases k <;> decide

/-- **A comparison site** branches on `a ≤ i`, leaving `d = min a i`. -/
theorem le_run (k : LeS) (st : St) (hbd : st.Bd B) (hd : st.d = 0) :
    AReach (A a b f mode) o y (GuardLe (A a b f mode) y B) (some (.le k 0), st.toV, none)
      (some (if st.toV (leReg k) ≤ st.i then leYes k else leNo k),
        Function.update st.toV rD (min (st.toV (leReg k)) st.i), none) :=
  Codec.le_loop (A a b f mode) o y rD (leReg k) rI (le_ne k) (by decide) (.le k 0) (.le k 1)
    (.le k 2) (leYes k) (leNo k) rfl rfl rfl B st.toV hbd.toV (by simp [hd]) (by simp [hd])

/-- **The halving site** `u := u / 2 ^ c`. -/
theorem hv_run (st : St) (hbd : st.Bd B) :
    AReach (A a b f mode) o y (GuardLe (A a b f mode) y B) (some (.hv 0), st.toV, none)
      (some (.cp .TU), St.toV { st with c := 0, u := st.u / 2 ^ st.c }, none) := by
  have h := halve_run (A := A a b f mode) (oracle := o) (x := y) (B := B) (c := rC) (r := rU)
    (l := .hv 0) (l1 := .hv 1) (l2 := .hv 2) (lx := .cp .TU)
    (by decide) rfl rfl rfl _ st.toV rfl hbd.toV
  regs at h
  exact h

end Complexity.PathHard
