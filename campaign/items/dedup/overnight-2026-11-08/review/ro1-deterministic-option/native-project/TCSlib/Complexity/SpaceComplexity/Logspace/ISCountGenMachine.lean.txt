/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountRegs
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountMath

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The window-growing inductive-counting register machine

The nondeterministic abstract register machine `Complexity.LogProg.ISGen.igA` runs the
inductive counting of Immerman and Szelepcsényi [AB09, §4.3.2, proof of Theorem 4.20 and
Corollary 4.21] on the configuration graph of a nondeterministic decider `N` of space `sp`
**without knowing `sp`**: it counts the reachable codes at the window radii
`s = 0, 1, 2, …` and stops at the first radius whose count equals the count at the previous
radius (`Complexity.ExpBFS.mem_iff_of_card_eq`: then the window is closed under steps and
acceptance is decided by the reachable codes). Since the counts agree above the space bound
(`Complexity.ExpBFS.card_rset_succ_of_le`), the radius never exceeds `sp |x| + 1`, so all
registers have `O(sp |x| + log |x|)` bits, and no space-constructibility of the bound is
needed.

It has the seventeen registers of `Complexity.LogProg.ISCount.St`
(`TCSlib.Complexity.SpaceComplexity.Logspace.ISCountRegs`) and the four deciders of the
Savitch machine (`Complexity.LogProg.SavitchARM.decs`: the input length and the initial,
accepting and step code languages).

* **Setup.** `n := |x|`, then `lg := size n + 1` (halving `n` down to `0`); the register `n`
  (now `0`) then serves as the previous count `prv`.
* **Radius loop.** At radius `s` (initially `0`): the exponent `e := 2E · lg + 2E · s` by
  `2E` add-twice rounds (`rd false` on `lg`, `rd true` on `s`), the code bound `K := 2 ^ e` by
  doubling, `i := 0`, `i1 := 1`, `cp := 1`, and the stages computing `cp = |C_K|` (the number
  of reachable codes at radius `s`, rejecting on accepting ones). Then (`cmp`) if `cp = prv`
  accept; otherwise `prv := cp`, `s := s + 1` and repeat.
* **Stages.** With `cp = |C_i|`, stage `i` computes `c = |C_{i+1}|`, where `C_j` is the set
  of codes `t < K` reachable from the initial code by at most `j` steps: for every `v < K` in
  ascending order it guesses whether `v ∈ C_{i+1}`. A member is certified by a guessed walk
  of at most `i + 1` steps (and must not be accepting); a non-member by enumerating, in
  ascending order, guessed members `u` of `C_i` with their walks, none equal to `v` or
  stepping to `v`, and checking that exactly `cp` were found.
* **Walks.** A walk guesses a start code `g < K`, checks it is initial, and repeatedly
  guesses a next code, checking the step pair, until it meets the target or runs out of
  steps; its scratch registers are cleared on success.

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ISGen.GLb`, `Complexity.LogProg.ISGen.igA` — the labels and the
  machine.
* `Complexity.LogProg.ISGen.IG` — the semantics at a label and register file.

## Main results

* `Complexity.LogProg.ISGen.igA_npreS` — the machine meets the syntactic preconditions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20, Corollary 4.21.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing ISCount

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The labels of the window-growing counting machine**: the setup, the add-twice rounds
of the exponent, the doubling, the stage start (five steps), the stages, the outer and inner
enumerations, the walks, and the radius-loop labels `cmp`, `nx*`. -/
inductive GLb (E : ℕ) where
  /-- setup: query the input-length decider at `n` -/
  | scan
  /-- setup: increment `n` -/
  | incN
  /-- setup: `lg := 1` -/
  | lg0
  /-- setup: test `n = 0` -/
  | hz
  /-- setup: halve `n` -/
  | hh
  /-- setup: increment `lg` -/
  | hi
  /-- a round with `j` rounds left (`ph`: add `2 lg` or `2 s` to `e`) -/
  | rd (ph : Bool) (j : Fin (E + 1))
  /-- the add-twice loop of a round: test -/
  | ak (ph : Bool) (j : Fin (E + 1))
  /-- the add-twice loop: first increment of `e` -/
  | ak1 (ph : Bool) (j : Fin (E + 1))
  /-- the add-twice loop: second increment of `e` -/
  | ak2 (ph : Bool) (j : Fin (E + 1))
  /-- the add-twice loop: increment the counter -/
  | ak3 (ph : Bool) (j : Fin (E + 1))
  /-- `K := 1` (after `K := 0`) -/
  | k1
  /-- doubling: test `e = 0` -/
  | db
  /-- doubling: decrement `e` -/
  | dd
  /-- doubling: clear `T` -/
  | dc1
  /-- doubling: clear `k` -/
  | dc2
  /-- doubling: add-twice test -/
  | dk
  /-- doubling: add-twice, first increment -/
  | dk1
  /-- doubling: add-twice, second increment -/
  | dk2
  /-- doubling: add-twice, counter increment -/
  | dk3
  /-- doubling: clear `K` -/
  | dcl
  /-- doubling: copy test -/
  | dcp
  /-- doubling: copy increment -/
  | dcb
  /-- counting: `i := 0` -/
  | st0
  /-- counting: `i1 := 0` -/
  | st1
  /-- counting: `i1 := 1` -/
  | st2
  /-- counting: `cp := 0` -/
  | st3
  /-- counting: `cp := 1` -/
  | st4
  /-- stage head: test `i = K` -/
  | sh
  /-- stage: clear `v` -/
  | sv
  /-- stage: clear `c` -/
  | sc
  /-- outer enumeration: test `v = K` -/
  | vh
  /-- outer enumeration: guess membership of `v` -/
  | vch
  /-- outer enumeration: query the accepting-code decider at `v` -/
  | vA
  /-- outer enumeration: count `v` -/
  | vC
  /-- outer enumeration: next `v` -/
  | vn
  /-- inner enumeration: clear `u` -/
  | uI
  /-- inner enumeration: clear `cnt` -/
  | uc
  /-- inner enumeration: test `u = K` -/
  | uh
  /-- inner enumeration: guess membership of `u` -/
  | uch
  /-- inner enumeration: test `u = v` -/
  | uE
  /-- inner enumeration: query the step decider at `(u, v)` -/
  | uS
  /-- inner enumeration: count `u` -/
  | uC
  /-- inner enumeration: next `u` -/
  | un
  /-- inner enumeration: test `cnt = cp` -/
  | ue
  /-- inner enumeration: clear `u` -/
  | ucl1
  /-- inner enumeration: clear `cnt` -/
  | ucl2
  /-- stage end: clear `cp` -/
  | se
  /-- stage end: copy test -/
  | sec
  /-- stage end: copy increment -/
  | sinc
  /-- stage end: increment `i` -/
  | si
  /-- stage end: increment `i1` -/
  | si1
  /-- radius loop: compare the count with the previous count -/
  | cmp
  /-- radius loop: clear `prv` -/
  | nx
  /-- radius loop: copy test `prv = cp` -/
  | nx1
  /-- radius loop: copy increment -/
  | nx2
  /-- radius loop: increment the radius -/
  | nx3
  /-- accept -/
  | acc
  /-- reject -/
  | rej
  /-- walk: clear `g` -/
  | w0 (b : Bool)
  /-- walk guess: test `g = K` -/
  | gt (b f : Bool)
  /-- walk guess: stop or go on -/
  | gc (b f : Bool)
  /-- walk guess: increment `g` -/
  | gm (b f : Bool)
  /-- walk: query the initial-code decider at `g` -/
  | gxI (b : Bool)
  /-- walk: query the step decider at `(cur, g)` -/
  | gxS (b : Bool)
  /-- walk: clear `cur` -/
  | wz (b f : Bool)
  /-- walk: copy test `cur = g` -/
  | wc (b f : Bool)
  /-- walk: copy increment -/
  | wcb (b f : Bool)
  /-- walk: clear `stp` -/
  | w2 (b : Bool)
  /-- walk loop: test `cur` against the target -/
  | wl (b : Bool)
  /-- walk loop: test `stp` against the bound -/
  | wl2 (b : Bool)
  /-- walk loop: clear `g` -/
  | wl3 (b : Bool)
  /-- walk loop: count the step -/
  | wst (b : Bool)
  /-- walk end: clear `cur` -/
  | wd (b : Bool)
  /-- walk end: clear `stp` -/
  | wd2 (b : Bool)
  /-- walk end: clear `g` -/
  | wd3 (b : Bool)
  deriving DecidableEq, Fintype

variable {E : ℕ}

/-- The exit of a walk: the accepting-code test (outer site) or the inequality test (inner
site). -/
def gwX (b : Bool) : GLb E := if b then .uE else .vA

/-- The exit of the walk copy loop: the step count reset (start) or the step count (step). -/
def gwcX (b f : Bool) : GLb E := if f then .wst b else .w2 b

/-- The last instruction of the rounds: after the `lg` rounds, start the `s` rounds; after
the `s` rounds, `K := 0` (then `K := 1` and doubling). -/
def grdX (ph : Bool) : Ins 17 4 (GLb E) :=
  if ph then .clr rK .k1 else .clr rk (.rd true (Fin.last E))

/-- **The window-growing counting machine** (constant `E`); deciders `0` (input length), `1`
(initial codes), `2` (accepting codes), `3` (step pairs); the register `n` holds the previous
count after the setup. See the module docstring. -/
def igA (E : ℕ) : NARM 17 4 (GLb E)
  | .scan => .det (.call 0 .whole [rn] .incN .lg0)
  | .incN => .det (.inc rn .scan)
  | .lg0 => .det (.inc rlg .hz)
  | .hz => .det (.jz rn (.rd false (Fin.last E)) .hh)
  | .hh => .det (.half rn .hi)
  | .hi => .det (.inc rlg .hz)
  | .rd ph j => .det (if j.val = 0 then grdX ph else .clr rk (.ak ph j))
  | .ak ph j => .det (.jeq rk (rY ph) (.rd ph ⟨j.val - 1, by omega⟩) (.ak1 ph j))
  | .ak1 ph j => .det (.inc re (.ak2 ph j))
  | .ak2 ph j => .det (.inc re (.ak3 ph j))
  | .ak3 ph j => .det (.inc rk (.ak ph j))
  | .k1 => .det (.inc rK .db)
  | .db => .det (.jz re .st0 .dd)
  | .dd => .det (.dec re .dc1)
  | .dc1 => .det (.clr rT .dc2)
  | .dc2 => .det (.clr rk .dk)
  | .dk => .det (.jeq rk rK .dcl .dk1)
  | .dk1 => .det (.inc rT .dk2)
  | .dk2 => .det (.inc rT .dk3)
  | .dk3 => .det (.inc rk .dk)
  | .dcl => .det (.clr rK .dcp)
  | .dcp => .det (.jeq rK rT .db .dcb)
  | .dcb => .det (.inc rK .dcp)
  | .st0 => .det (.clr ri .st1)
  | .st1 => .det (.clr ri1 .st2)
  | .st2 => .det (.inc ri1 .st3)
  | .st3 => .det (.clr rcp .st4)
  | .st4 => .det (.inc rcp .sh)
  | .sh => .det (.jeq ri rK .cmp .sv)
  | .sv => .det (.clr rv .sc)
  | .sc => .det (.clr rc .vh)
  | .vh => .det (.jeq rv rK .se .vch)
  | .vch => .choose (.w0 false) .uI
  | .vA => .det (.call 2 .whole [rv, rs] .rej .vC)
  | .vC => .det (.inc rc .vn)
  | .vn => .det (.inc rv .vh)
  | .uI => .det (.clr ru .uc)
  | .uc => .det (.clr rcnt .uh)
  | .uh => .det (.jeq ru rK .ue .uch)
  | .uch => .choose (.w0 true) .un
  | .uE => .det (.jeq ru rv .rej .uS)
  | .uS => .det (.call 3 .whole [ru, rv, rs] .rej .uC)
  | .uC => .det (.inc rcnt .un)
  | .un => .det (.inc ru .uh)
  | .ue => .det (.jeq rcnt rcp .ucl1 .rej)
  | .ucl1 => .det (.clr ru .ucl2)
  | .ucl2 => .det (.clr rcnt .vn)
  | .se => .det (.clr rcp .sec)
  | .sec => .det (.jeq rcp rc .si .sinc)
  | .sinc => .det (.inc rcp .sec)
  | .si => .det (.inc ri .si1)
  | .si1 => .det (.inc ri1 .sh)
  | .cmp => .det (.jeq rcp rn .acc .nx)
  | .nx => .det (.clr rn .nx1)
  | .nx1 => .det (.jeq rn rcp .nx3 .nx2)
  | .nx2 => .det (.inc rn .nx1)
  | .nx3 => .det (.inc rs (.rd false (Fin.last E)))
  | .acc => .det (.ret true)
  | .rej => .det (.ret false)
  | .w0 b => .det (.clr rg (.gt b false))
  | .gt b f => .det (.jeq rg rK .rej (.gc b f))
  | .gc b f => .choose (if f then .gxS b else .gxI b) (.gm b f)
  | .gm b f => .det (.inc rg (.gt b f))
  | .gxI b => .det (.call 1 .whole [rg, rs] (.wz b false) .rej)
  | .gxS b => .det (.call 3 .whole [rcur, rg, rs] (.wz b true) .rej)
  | .wz b f => .det (.clr rcur (.wc b f))
  | .wc b f => .det (.jeq rcur rg (gwcX b f) (.wcb b f))
  | .wcb b f => .det (.inc rcur (.wc b f))
  | .w2 b => .det (.clr rstp (.wl b))
  | .wl b => .det (.jeq rcur (wT b) (.wd b) (.wl2 b))
  | .wl2 b => .det (.jeq rstp (wB b) .rej (.wl3 b))
  | .wl3 b => .det (.clr rg (.gt b true))
  | .wst b => .det (.inc rstp (.wl b))
  | .wd b => .det (.clr rcur (.wd2 b))
  | .wd2 b => .det (.clr rstp (.wd3 b))
  | .wd3 b => .det (.clr rg (gwX b))

/-- **The machine meets the syntactic preconditions**: its comparisons are of distinct
registers and the arguments of its calls are distinct. -/
lemma igA_npreS (x : List Bool) (a : AConf 17 (GLb E)) : NPreS (igA E) x a := by
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · cases l
    case rd ph j =>
      simp only [NPreS, PreS, NARM.detPart, igA]
      split_ifs <;> cases ph <;> simp [grdX]
    all_goals simp [NPreS, PreS, NARM.detPart, igA, rn, rlg, rk, rs, re, rK, rT, ri, ri1,
      rcp, rv, rc, ru, rcnt, rg, rcur, rstp]
    all_goals first
      | (rename_i ph j; cases ph <;> simp [rY, rs, rlg])
      | (rename_i b; cases b <;> simp [wT, wB, ru, rv, ri, ri1])

/-- The semantics of the window-growing counting machine for the deciders' answers `orc`, at
label `l` with register file `σ`, every register at most `B`. -/
abbrev IG (orc : Fin 4 → List Bool → Bool) (x : List Bool) (B : ℕ) (l : GLb E) (σ : St)
    (P : Prop) : Prop :=
  NSem (igA E) orc x (RegLe 17 (GLb E) B) (some l, σ.toV, none) P

/-- A bounded register file meets the register-bound guard. -/
lemma St.greg {σ : St} {B : ℕ} (h : σ.Bd B) (l : Option (GLb E)) (res : Option Bool) :
    RegLe 17 (GLb E) B (l, σ.toV, res) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  intro r
  fin_cases r <;> assumption

/-- Change the register file to an equal one. -/
lemma IG.of_eq {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B : ℕ} {l : GLb E}
    {σ σ' : St} {P : Prop} (h : σ = σ') (hp : IG orc x B l σ' P) : IG orc x B l σ P :=
  h ▸ hp

end ISGen

end Complexity.LogProg
