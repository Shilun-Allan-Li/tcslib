/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract register machines

Logspace algorithms are usually described with a constant number of counters of logarithmic
size [AB09, §4.1]. An *abstract register machine* (`Complexity.LogProg.ARM`) is a flowchart
over finitely many labels whose registers hold natural numbers, with the instructions:
increment, decrement, clear, halve, zero/parity/equality tests, the input-format checks and
index comparisons of `TCSlib.Complexity.SpaceComplexity.Machines.Parse`, subroutine calls,
and `ret b` (answer `b`). Its semantics (`Complexity.LogProg.astep`) is over values; the
compilation `Complexity.LogProg.armProg` into a register-tape program stores each register
in binary (`Nat.bits`) and implements each instruction by the fragment proved for it.

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Main definitions

* `Complexity.LogProg.Ins`, `Complexity.LogProg.ARM` — instructions and machines.
* `Complexity.LogProg.astep` — the value semantics.
* `Complexity.LogProg.armProg` — the compiled register-tape program.
* `Complexity.LogProg.aseam` — the program configuration of an abstract configuration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-- The instructions of an abstract register machine over `m` registers calling `d` deciders,
with labels `Λ`. -/
inductive Ins (m d : ℕ) (Λ : Type) where
  /-- `r := r + 1` -/
  | inc (r : Fin m) (l : Λ)
  /-- `r := r - 1` (truncated) -/
  | dec (r : Fin m) (l : Λ)
  /-- `r := 0` -/
  | clr (r : Fin m) (l : Λ)
  /-- `r := r / 2` -/
  | half (r : Fin m) (l : Λ)
  /-- branch on `r = 0` -/
  | jz (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `r` odd -/
  | jodd (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `r = s` (distinct registers) -/
  | jeq (r s : Fin m) (l₁ l₀ : Λ)
  /-- call decider `j` on the virtual input of `mode` and `args` -/
  | call (j : Fin d) (mode : Mode) (args : List (Fin m)) (l₁ l₀ : Λ)
  /-- answer `b` and halt -/
  | ret (b : Bool)
  /-- check that the input is `⟨1ⁿ, w⟩` with `w` a canonical binary payload (a `Nat.bits`
  word — `pairEncode [] [false]` has the pair shape but is rejected); else answer `0`;
  `r` is any register -/
  | valP (r : Fin m) (l : Λ)
  /-- check that the input is `⟨1ⁿ, ⟨u, w⟩⟩` with both inner payloads canonical binary
  words (else answer `0`) -/
  | valQ (r : Fin m) (l : Λ)
  /-- branch on `Nat.bits r = w` for the input `⟨1ⁿ, w⟩` -/
  | jeqIn (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `Nat.bits r = u` for the input `⟨1ⁿ, ⟨u, w⟩⟩` -/
  | jeqFst (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `Nat.bits r = w` for the input `⟨1ⁿ, ⟨u, w⟩⟩` -/
  | jeqSnd (r : Fin m) (l₁ l₀ : Λ)

/-- An abstract register machine: an instruction at every label. -/
abbrev ARM (m d : ℕ) (Λ : Type) := Λ → Ins m d Λ

/-- The word `w` of an input `⟨1ⁿ, w⟩`. -/
def plainWord (x : List Bool) : List Bool := x.drop (tRun x + 2)

/-- The words `u`, `w` of an input `⟨1ⁿ, ⟨u, w⟩⟩`. -/
def pairWords (x : List Bool) : List Bool × List Bool :=
  (pairDecode (x.drop (tRun x + 2))).getD ([], [])

/-- The word of the input `⟨1ⁿ, w⟩` is `w`. -/
lemma plainWord_pairEncode (n : ℕ) (w : List Bool) :
    plainWord (pairEncode (List.replicate n true) w) = w := by
  unfold plainWord
  rw [tRun_pairEncode]
  simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append]

/-- The words of the input `⟨1ⁿ, ⟨u, w⟩⟩` are `u` and `w`. -/
lemma pairWords_pairEncode (n : ℕ) (u w : List Bool) :
    pairWords (pairEncode (List.replicate n true) (pairEncode u w)) = (u, w) := by
  have : (pairEncode (List.replicate n true) (pairEncode u w)).drop
      (tRun (pairEncode (List.replicate n true) (pairEncode u w)) + 2) = pairEncode u w := by
    rw [tRun_pairEncode]; simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append]
  simp [pairWords, this, pairDecode_pairEncode]

/-- An abstract configuration: the current label (`none` when halted), the register values,
and the answer once halted. -/
abbrev AConf (m : ℕ) (Λ : Type) := Option Λ × (Fin m → ℕ) × Option Bool

open Classical in
/-- **One step of an abstract register machine** on input `x`, deciders answering `oracle`. -/
noncomputable def astep {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) : AConf m Λ → AConf m Λ
  | (none, v, res) => (none, v, res)
  | (some l, v, res) =>
    match A l with
    | .inc r l' => (some l', Function.update v r (v r + 1), res)
    | .dec r l' => (some l', Function.update v r (v r - 1), res)
    | .clr r l' => (some l', Function.update v r 0, res)
    | .half r l' => (some l', Function.update v r (v r / 2), res)
    | .jz r l₁ l₀ => (some (if v r = 0 then l₁ else l₀), v, res)
    | .jodd r l₁ l₀ => (some (if v r % 2 = 1 then l₁ else l₀), v, res)
    | .jeq r s l₁ l₀ => (some (if v r = v s then l₁ else l₀), v, res)
    | .call j md args l₁ l₀ =>
      (some (if oracle j (vword (callSegs ⟨j, md, args, l₁, l₀⟩ x (fun r => Nat.bits (v r))))
        then l₁ else l₀), v, res)
    | .ret b => (none, v, some b)
    | .valP _ l' => if ValidPlain x then (some l', v, res) else (none, v, some false)
    | .valQ _ l' => if ValidPair x then (some l', v, res) else (none, v, some false)
    | .jeqIn r l₁ l₀ => (some (if Nat.bits (v r) = plainWord x then l₁ else l₀), v, res)
    | .jeqFst r l₁ l₀ => (some (if Nat.bits (v r) = (pairWords x).1 then l₁ else l₀), v, res)
    | .jeqSnd r l₁ l₀ => (some (if Nat.bits (v r) = (pairWords x).2 then l₁ else l₀), v, res)

/-- The run of an abstract register machine. -/
noncomputable def arun {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) (a : AConf m Λ) (n : ℕ) : AConf m Λ :=
  (astep A oracle x)^[n] a

/-! ## Compilation -/

/-- The phases of the instruction fragments. -/
inductive Ph where
  | start
  | incB
  | decL | decE | decB
  | clrE
  | h0 | hF | hT
  | eqBy | eqBn
  | vU1 | vS | vW0 | vWF | vWT | vrw1 | vrw2
  | vP1 (l : Option Bool) | vP2 (b : Bool) (l : Option Bool)
  | jK2 | jC | jRB (b : Bool) | jI1 (b : Bool) | jI2 (b : Bool)
  | jP1 | jP2F | jP2T | jD1 | jD2F | jD2T
  deriving DecidableEq, Fintype

/-- A control action: change state, move nothing. -/
def goAct {m : ℕ} {S : Type} (s : S) : Action m Bool S := ⟨0, fun _ => (none, 0), none, some s⟩

/-- Halt with output `b`. -/
def retAct {m : ℕ} {S : Type} (b : Bool) : Action m Bool S := ⟨0, fun _ => (none, 0), some b, none⟩

/-- The input rewind scan (moving nothing else): left over symbols, then right into `nx`. -/
def rw2Act {m : ℕ} {S : Type} (r : Fin m) (s₀ nx : S) (a : Option Bool) : Action m Bool S :=
  match a with
  | some _ => xAct r (-1) 0 s₀
  | none => xAct r 1 0 nx

/-- The halting junk action. -/
def junkAct {m : ℕ} {S : Type} : Action m Bool S := ⟨0, fun _ => (none, 0), none, none⟩

/-- **The transition table of one instruction's fragment**: phase `start` is the fragment's
first state. -/
def insTr {m d : ℕ} {Λ : Type} (i : Ins m d Λ) (l : Λ) (ph : Ph) (a : Option Bool)
    (w : Fin m → Option Bool) : Action m Bool (Λ × Ph) :=
  match i with
  | .inc r l' =>
    match ph with
    | .start => incCAct r (l, .start) (l, .incB) (w r)
    | .incB => incBAct r (l, .incB) (l', .start) (w r)
    | _ => junkAct
  | .dec r l' =>
    match ph with
    | .start => decDAct r (l, .start) (l, .decL) (l, .decB) (w r)
    | .decL => decLAct r (l, .decE) (l, .decB) (w r)
    | .decE => decEAct r (l, .decB)
    | .decB => incBAct r (l, .decB) (l', .start) (w r)
    | _ => junkAct
  | .clr r l' =>
    match ph with
    | .start => toEndAct r (l, .start) (l, .clrE) (w r)
    | .clrE => clrEAct r (l, .clrE) (l', .start) (w r)
    | _ => junkAct
  | .half r l' =>
    match ph with
    | .start => toEndAct r (l, .start) (l, .h0) (w r)
    | .h0 => halfLAct r none (l, .hF) (l, .hT) (l', .start) (w r)
    | .hF => halfLAct r (some false) (l, .hF) (l, .hT) (l', .start) (w r)
    | .hT => halfLAct r (some true) (l, .hF) (l, .hT) (l', .start) (w r)
    | _ => junkAct
  | .jz r l₁ l₀ =>
    match ph with
    | .start => goAct (if w r = none then (l₁, .start) else (l₀, .start))
    | _ => junkAct
  | .jodd r l₁ l₀ =>
    match ph with
    | .start => goAct (if w r = some true then (l₁, .start) else (l₀, .start))
    | _ => junkAct
  | .jeq r s l₁ l₀ =>
    match ph with
    | .start => eqCAct r s (l, .start) (l, .eqBy) (l, .eqBn) (w r) (w s)
    | .eqBy => eqBAct r s (l, .eqBy) (l₁, .start) (w r)
    | .eqBn => eqBAct r s (l, .eqBn) (l₀, .start) (w r)
    | _ => junkAct
  | .call _ _ _ _ _ => junkAct
  | .ret b =>
    match ph with
    | .start => retAct b
    | _ => junkAct
  | .valP r l' =>
    match ph with
    | .start => valUAct r (l, .start) (l, .vU1) (l, .vS) false a
    | .vU1 => valUAct r (l, .start) (l, .vU1) (l, .vS) true a
    | .vS => valSAct r (l, .vW0) a
    | .vW0 => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) none a
    | .vWF => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some false) a
    | .vWT => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some true) a
    | .vrw1 => xAct r (-1) 0 (l, .vrw2)
    | .vrw2 => rw2Act r (l, .vrw2) (l', .start) a
    | _ => junkAct
  | .valQ r l' =>
    match ph with
    | .start => valUAct r (l, .start) (l, .vU1) (l, .vS) false a
    | .vU1 => valUAct r (l, .start) (l, .vU1) (l, .vS) true a
    | .vS => valSAct r (l, .vP1 none) a
    | .vP1 lst => valP1Act r (fun b => (l, .vP2 b lst)) a
    | .vP2 b lst => valP2Act r (l, .vP1 (some false)) (l, .vP1 (some true)) (l, .vW0) lst b a
    | .vW0 => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) none a
    | .vWF => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some false) a
    | .vWT => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some true) a
    | .vrw1 => xAct r (-1) 0 (l, .vrw2)
    | .vrw2 => rw2Act r (l, .vrw2) (l', .start) a
    | _ => junkAct
  | .jeqIn r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jC)
    | .jC => cmpAct r (l, .jC) (fun b => (l, .jRB b)) a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct
  | .jeqSnd r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jP1)
    | .jP1 => pskip1Act r (l, .jP2F) (l, .jP2T) a
    | .jP2F => pskip2Act r (l, .jP1) (l, .jC) false a
    | .jP2T => pskip2Act r (l, .jP1) (l, .jC) true a
    | .jC => cmpAct r (l, .jC) (fun b => (l, .jRB b)) a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct
  | .jeqFst r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jD1)
    | .jD1 => dcmp1Act r (l, .jD2F) (l, .jD2T) a
    | .jD2F => dcmp2Act r (l, .jD1) (fun b => (l, .jRB b)) false a (w r)
    | .jD2T => dcmp2Act r (l, .jD1) (fun b => (l, .jRB b)) true a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct

/-- The transition table of the compiled program. -/
def armTr {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (l : Λ) (ph : Ph) (a : Option Bool)
    (w : Fin m → Option Bool) : Action m Bool (Λ × Ph) :=
  insTr (A l) l ph a w

/-- The call node of one instruction. -/
def insCall {m d : ℕ} {Λ : Type} (i : Ins m d Λ) (ph : Ph) : Option (CallSpec m d (Λ × Ph)) :=
  match i with
  | .call j md args l₁ l₀ =>
    match ph with
    | .start => some ⟨j, md, args, (l₁, .start), (l₀, .start)⟩
    | _ => none
  | _ => none

/-- The call nodes of the compiled program. -/
def armCall {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (q : Λ × Ph) :
    Option (CallSpec m d (Λ × Ph)) :=
  insCall (A q.1) q.2

/-- **The compiled register-tape program** of an abstract register machine. -/
def armProg {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (l₀ : Λ) : RProg m d (Λ × Ph) where
  tm := ⟨(l₀, .start), fun q a w => armTr A q.1 q.2 a w⟩
  call := armCall A

/-- The program configuration representing the abstract configuration at label `l` with
values `v`, having written `out`. -/
def aseam {m : ℕ} {Λ : Type} (x : List Bool) (l : Λ) (v : Fin m → ℕ) (out : List Bool) :
    Cfg m Bool (Λ × Ph) x :=
  ⟨some (l, .start), ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)), fun _ => 0, out⟩

end Complexity.LogProg
