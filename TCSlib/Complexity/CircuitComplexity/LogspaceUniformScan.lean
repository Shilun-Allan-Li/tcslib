/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdjBasic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Scanning a circuit description in logarithmic space

The "only if" half of [AB09, p. 112]'s robustness remark: from the bits of the description
`BoolCircuit.DAGCircuit.encode Cₙ` (available through the bit language of an implicitly
logspace computable function), `SIZE`, `TYPE` and `EDGE` are decided by scanning the
description with a position counter, a vertex counter and an argument counter.

The scanner is one abstract register machine `BoolCircuit.AdjScan.scan τ` for the three
tasks `τ`; this file proves its run (`BoolCircuit.AdjScan.scan_halts`): it answers
`nAns τ` when the target vertex is an input, `hitAns τ i g` when it is the gate `g`, and
`false` beyond the circuit.

## Main definitions

* `BoolCircuit.AdjScan.Task` — `SIZE`, `TYPE t` or `EDGE`.
* `BoolCircuit.AdjScan.scan` — the scanner.

## Main results

* `BoolCircuit.AdjScan.scan_halts` — the scanner's answer on a well-formed description.

File size: about 650 lines, over the 600-line target. The file is one abstract machine
with the run lemmas of its nested loops, which all rely on the machine's definition and step
lemmas. The language-level theorems are in
`TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdj`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.2.1, p. 112.)
-/

namespace BoolCircuit

namespace AdjScan

open Turing Complexity LogProg

/-- The three scanning tasks. -/
inductive Task where
  | size
  | type (t : Option GateKind)
  | edge

/-- The labels of the scanner. -/
inductive Lbl where
  | start | nA | nB | nHit | nC | nD | nE
  | gA | gB | gC | gD | sK1 | sK2
  | aA (ex : Bool) | aB (ex : Bool) | aC (ex : Bool) | aEnd (ex : Bool)
  | uA (ex : Bool) | uB (ex : Bool) | uC (ex : Bool) | uE (ex : Bool) | uF
  | hHit | eK1 | eK2
  | kA | kB (b : Bool) | kC (b : Bool) | kD (b₁ b₂ : Bool)
  | acc | rej
  deriving DecidableEq, Fintype

/-- The gate label of a two-bit code. -/
def decodeKind : Bool → Bool → GateKind
  | false, false => .and
  | false, true => .or
  | true, _ => .not

/-- Read the description bit at the position register `0`. -/
def rd (l₁ l₀ : Lbl) : Ins 3 1 Lbl := .call 0 .unaryFst [0] l₁ l₀

/-- Compare the vertex register `1` with the target vertex. -/
def hit : Task → Lbl → Lbl → Ins 3 1 Lbl
  | .edge, l₁, l₀ => .jeqSnd 1 l₁ l₀
  | _, l₁, l₀ => .jeqIn 1 l₁ l₀

/-- The answer when the target vertex is an input. -/
def nAns : Task → Bool
  | .size => true
  | .type t => decide (t = none)
  | .edge => false

/-- The answer when the target vertex is the gate `g` (`i` the source vertex of `EDGE`). -/
def hitAns (i : ℕ) (g : DAGGate) : Task → Bool
  | .size => true
  | .type t => decide (t = some g.kind)
  | .edge => decide (i ∈ g.args)

/-- **The scanner** for task `τ`. Registers: `0` the position in the description, `1` the
vertex counter, `2` the argument counter. -/
def scan (τ : Task) : ARM 3 1 Lbl
  | .start => match τ with
    | .edge => .valQ 0 .nA
    | _ => .valP 0 .nA
  | .nA => rd .nB .nE
  | .nB => hit τ .nHit .nC
  | .nHit => .ret (nAns τ)
  | .nC => .inc 1 .nD
  | .nD => .inc 0 .nA
  | .nE => .inc 0 .gA
  | .gA => rd .gB .rej
  | .gB => hit τ .hHit .gC
  | .gC => .inc 1 .gD
  | .gD => .inc 0 .sK1
  | .sK1 => .inc 0 .sK2
  | .sK2 => .inc 0 (.aA false)
  | .aA ex => rd (.aB ex) (.aEnd ex)
  | .aEnd ex => if ex then .ret false else .inc 0 .gA
  | .aB ex => .inc 0 (.aC ex)
  | .aC ex => .clr 2 (.uA ex)
  | .uA ex => rd (.uB ex) (.uE ex)
  | .uB ex => .inc 2 (.uC ex)
  | .uC ex => .inc 0 (.uA ex)
  | .uE ex => if ex then (match τ with
      | .edge => .jeqFst 2 .acc .uF
      | _ => .ret false)
    else .inc 0 (.aA false)
  | .uF => .inc 0 (.aA true)
  | .hHit => match τ with
    | .size => .ret true
    | .type _ => .inc 0 .kA
    | .edge => .inc 0 .eK1
  | .eK1 => .inc 0 .eK2
  | .eK2 => .inc 0 (.aA true)
  | .kA => rd (.kB true) (.kB false)
  | .kB b => .inc 0 (.kC b)
  | .kC b => rd (.kD b true) (.kD b false)
  | .kD b₁ b₂ => .ret (match τ with
    | .type t => decide (t = some (decodeKind b₁ b₂))
    | _ => false)
  | .acc => .ret true
  | .rej => .ret false

/-! ## Registers -/

/-- The register file `(p, c, a)`. -/
def rg (p c a : ℕ) : Fin 3 → ℕ := ![p, c, a]

/-- Register `0` of `rg p c a` is the position `p`. -/
@[simp] lemma rg_zero (p c a : ℕ) : rg p c a 0 = p := rfl
/-- Register `1` of `rg p c a` is the vertex counter `c`. -/
@[simp] lemma rg_one (p c a : ℕ) : rg p c a 1 = c := rfl
/-- Register `2` of `rg p c a` is the argument counter `a`. -/
@[simp] lemma rg_two (p c a : ℕ) : rg p c a 2 = a := rfl

/-- A property of all three registers follows from the property of each. -/
lemma fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ r, P r
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2

/-- Setting register `0` of `rg p c a` to `q` gives `rg q c a`. -/
@[simp] lemma upd_zero (p c a q : ℕ) : Function.update (rg p c a) 0 q = rg q c a := by
  funext r; revert r; refine fin3_cases ?_ ?_ ?_ <;> rfl
/-- Setting register `1` of `rg p c a` to `q` gives `rg p q a`. -/
@[simp] lemma upd_one (p c a q : ℕ) : Function.update (rg p c a) 1 q = rg p q a := by
  funext r; revert r; refine fin3_cases ?_ ?_ ?_ <;> rfl
/-- Setting register `2` of `rg p c a` to `q` gives `rg p c q`. -/
@[simp] lemma upd_two (p c a q : ℕ) : Function.update (rg p c a) 2 q = rg p c q := by
  funext r; revert r; refine fin3_cases ?_ ?_ ?_ <;> rfl

/-- The all-zero register file is `rg 0 0 0`. -/
lemma rg_init : (fun _ : Fin 3 => 0) = rg 0 0 0 := by
  funext r; revert r; refine fin3_cases ?_ ?_ ?_ <;> rfl

/-- The guard: every register at most `B`. -/
def Gd (B : ℕ) (a : AConf 3 Lbl) : Prop := ∀ r, a.2.1 r ≤ B

/-- A configuration whose registers are all at most `B` satisfies the guard `Gd B`. -/
lemma gd_rg {B p c a : ℕ} {l : Option Lbl} {res : Option Bool} (hp : p ≤ B) (hc : c ≤ B)
    (ha : a ≤ B) : Gd B (l, rg p c a, res) := by
  intro r; revert r; refine fin3_cases ?_ ?_ ?_ <;> simpa

/-! ## Steps -/

section Steps

variable {τ : Task} {n : ℕ} {w E : List Bool} {o : Fin 1 → List Bool → Bool}

/-- The input `⟨1ⁿ, w⟩`. -/
abbrev X (n : ℕ) (w : List Bool) : List Bool := pairEncode (List.replicate n true) w

/-- How the target vertex `tv` (and, for `EDGE`, the source vertex `iv`) sit in the input. -/
def Target (τ : Task) (x : List Bool) (iv tv : ℕ) : Prop :=
  match τ with
  | .edge => pairWords x = (Nat.bits iv, Nat.bits tv)
  | _ => plainWord x = Nat.bits tv

/-- A read step at position `p` branches on description bit `p` (the bit oracle answering
with `E`). -/
lemma astep_rd (hrd : ∀ p, o 0 (X n (Nat.bits p)) = E.getD p false) (l l₁ l₀ : Lbl)
    (hl : scan τ l = rd l₁ l₀) (p c a : ℕ) :
    astep (scan τ) o (X n w) (some l, rg p c a, none) =
      (some (if E.getD p false then l₁ else l₀), rg p c a, none) := by
  simp only [astep, hl, rd]
  rw [vword_unary₁]
  simp [hrd]

/-- A hit test branches on whether the vertex counter is the target vertex. -/
lemma astep_hit {iv tv : ℕ} (ht : Target τ (X n w) iv tv) (l l₁ l₀ : Lbl)
    (hl : scan τ l = hit τ l₁ l₀) (p c a : ℕ) :
    astep (scan τ) o (X n w) (some l, rg p c a, none) =
      (some (if c = tv then l₁ else l₀), rg p c a, none) := by
  cases τ <;> simp only [Target] at ht <;>
    simp [astep, hl, hit, ht, bits_injective.eq_iff]

/-- The argument test of `EDGE` branches on whether the argument counter is the source vertex. -/
lemma astep_jeqFst {iv tv : ℕ} (ht : Target .edge (X n w) iv tv) (p c a : ℕ) :
    astep (scan .edge) o (X n w) (some (.uE true), rg p c a, none) =
      (some (if a = iv then .acc else .uF), rg p c a, none) := by
  simp only [Target] at ht
  simp [astep, scan, ht, bits_injective.eq_iff]

end Steps

/-! ## Description bits -/

/-- If `E` continues with `b` at position `p`, bit `p` of `E` is `b`. -/
lemma getD_of_drop {E rest : List Bool} {p : ℕ} {b : Bool} (h : E.drop p = b :: rest) :
    E.getD p false = b := by
  have : (E.drop p)[0]? = some b := by rw [h]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at this
  simp [List.getD_eq_getElem?_getD, this]

/-- If `E` continues with a nonempty `s` at position `p`, then `p + |s| ≤ |E|`. -/
lemma le_of_drop {E s rest : List Bool} {p : ℕ} (h : E.drop p = s ++ rest) (hs : s ≠ []) :
    p + s.length ≤ E.length := by
  have hs' : 0 < s.length := List.length_pos_iff.mpr hs
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  have hs : s.length ≤ E.length - p := by omega
  by_cases hp : p ≤ E.length
  · omega
  · have : E.drop p = [] := List.drop_of_length_le (by omega)
    rw [this] at h
    have := congrArg List.length h
    simp at this
    omega

/-- If `E` continues with `b :: rest` at position `p`, it continues with `rest` at `p + 1`. -/
lemma drop_succ_of_drop {E rest : List Bool} {p : ℕ} {b : Bool} (h : E.drop p = b :: rest) :
    E.drop (p + 1) = rest := by
  rw [← List.drop_drop, h]; rfl

/-- If `E` continues with `s ++ rest` at position `p`, it continues with `rest` at `p + |s|`. -/
lemma drop_add_of_drop {E s rest : List Bool} {p : ℕ} (h : E.drop p = s ++ rest) :
    E.drop (p + s.length) = rest := by
  rw [← List.drop_drop, h]; simp

/-- If `E` continues with `1ᵏ0` at position `p`, bit `p + j` (for `j ≤ k`) is `1` iff `j < k`. -/
lemma bit_rep {E rest : List Bool} {p k j : ℕ}
    (h : E.drop p = List.replicate k true ++ false :: rest) (hj : j ≤ k) :
    E.getD (p + j) false = decide (j < k) := by
  have e : E[p + j]? = (List.replicate k true ++ false :: rest)[j]? := by
    rw [← h, List.getElem?_drop]
  rw [List.getD_eq_getElem?_getD, e]
  rcases Nat.lt_or_ge j k with hl | hl
  · rw [List.getElem?_append_left (by simpa using hl)]; simp [hl]
  · obtain rfl : j = k := by omega
    rw [List.getElem?_append_right (by simp)]; simp

/-! ## The loops -/

section Loops

variable {τ : Task} {n : ℕ} {w E : List Bool} {o : Fin 1 → List Bool → Bool}

/-- **Reading a unary number**: from `uA` on `1ᵏ0`, the argument counter counts to `k`.

**Proof sketch.** Induction on the number `k - j` of `1`s left: each `1` is read, counted in the
argument register and skipped (`bit_rep`); the `0` ends the loop in `uE`. The registers stay
below `|E|` because the unary number lies inside `E`. -/
lemma uloop (hrd : ∀ p, o 0 (X n (Nat.bits p)) = E.getD p false) {B p c k : ℕ}
    {rest : List Bool} (ex : Bool) (h : E.drop p = List.replicate k true ++ false :: rest)
    (hB : E.length ≤ B) (hc : c ≤ B) :
    AReach (scan τ) o (X n w) (Gd B) (some (.uA ex), rg p c 0, none)
      (some (.uE ex), rg (p + k) c k, none) := by
  have hl := le_of_drop (s := List.replicate k true ++ [false]) (rest := rest) (by simpa using h)
    (by simp)
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hl
  have key : ∀ d j, j + d = k → AReach (scan τ) o (X n w) (Gd B)
      (some (.uA ex), rg (p + j) c j, none) (some (.uE ex), rg (p + k) c k, none) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      obtain rfl : j = k := by omega
      refine AReach.step (gd_rg (by omega) hc (by omega)) ?_
      rw [astep_rd hrd _ _ _ rfl, bit_rep h le_rfl]
      simpa using AReach.refl _
    | succ d ih =>
      intro j hj
      refine AReach.step (gd_rg (by omega) hc (by omega)) ?_
      rw [astep_rd hrd _ _ _ rfl, bit_rep h (by omega)]
      simp only [show j < k from by omega, decide_true, ↓reduceIte]
      refine AReach.step (gd_rg (by omega) hc (by omega)) ?_
      simp only [astep, scan, rg_two, upd_two]
      refine AReach.step (gd_rg (by omega) hc (by omega)) ?_
      simp only [astep, scan, rg_zero, upd_zero]
      exact ih (j + 1) (by omega)
  simpa using key k 0 (by omega)

/-- The code of `a :: as` is a `1`, the code of `a`, and the code of `as`. -/
lemma length_encodeList_cons {α : Type} (f : α → List Bool) (a : α) (as : List α) :
    (encodeList f (a :: as)).length = 1 + (f a).length + (encodeList f as).length := by
  simp [encodeList]; omega

/-- **Skipping an argument list.**

**Proof sketch.** Induction on the argument list. The list end `0` is skipped into `gA`. An
argument `1 1ᵏ 0` is skipped by reading the leading `1`, clearing the argument register and
running the unary loop (`uloop`), then skipping the `0`. -/
lemma argsSkip (hrd : ∀ p, o 0 (X n (Nat.bits p)) = E.getD p false) {B : ℕ}
    (hB : E.length ≤ B) (as : List ℕ) :
    ∀ {p c a : ℕ} {rest : List Bool}, E.drop p = encodeList encodeNat as ++ rest → c ≤ B →
      a ≤ B → ∃ a' ≤ B, AReach (scan τ) o (X n w) (Gd B) (some (.aA false), rg p c a, none)
        (some .gA, rg (p + (encodeList encodeNat as).length) c a', none) := by
  induction as with
  | nil =>
    intro p c a rest h hc ha
    have hl := le_of_drop h (by simp [encodeList])
    simp only [encodeList, List.length_singleton] at hl h ⊢
    refine ⟨a, ha, ?_⟩
    refine AReach.step (gd_rg (by omega) hc ha) ?_
    rw [astep_rd hrd _ _ _ rfl, getD_of_drop (by simpa using h)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AReach.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, Bool.false_eq_true, ↓reduceIte, rg_zero, upd_zero]
    exact AReach.refl _
  | cons k as ih =>
    intro p c a rest h hc ha
    have hl := le_of_drop h (by simp [encodeList])
    rw [length_encodeList_cons] at hl ⊢
    simp only [encodeNat, List.length_append, List.length_replicate,
      List.length_singleton] at hl ⊢
    simp only [encodeList, encodeNat, List.cons_append, List.append_assoc] at h
    have h1 := drop_succ_of_drop h
    have hu := drop_add_of_drop (s := List.replicate k true ++ [false]) (by simpa using h1)
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hu
    obtain ⟨a', ha', hr⟩ := ih (p := p + 1 + (k + 1)) (c := c) (a := k) (by rw [hu]) hc
      (by omega)
    refine ⟨a', ha', ?_⟩
    refine AReach.step (gd_rg (by omega) hc ha) ?_
    rw [astep_rd hrd _ _ _ rfl, getD_of_drop h]
    simp only [↓reduceIte]
    refine AReach.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, rg_zero, upd_zero]
    refine AReach.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, upd_two]
    refine (uloop hrd false h1 hB hc).trans ?_
    refine AReach.step (gd_rg (by omega) hc (by omega)) ?_
    simp only [astep, scan, Bool.false_eq_true, ↓reduceIte, rg_zero, upd_zero]
    convert hr using 4
    omega

/-- **Examining an argument list** (`EDGE`): the answer is whether the source vertex is an
argument.

**Proof sketch.** Induction on the argument list. At the list end the scanner answers `false`.
For an argument `k` it counts `k` with the unary loop and compares it with the source vertex
(`astep_jeqFst`): on equality it answers `true`, otherwise it continues with the rest, and `iv ∈
k :: as ↔ iv = k ∨ iv ∈ as`. -/
lemma argsEx {iv tv : ℕ} (hrd : ∀ p, o 0 (X n (Nat.bits p)) = E.getD p false)
    (ht : Target .edge (X n w) iv tv) {B : ℕ} (hB : E.length ≤ B) (as : List ℕ) :
    ∀ {p c a : ℕ} {rest : List Bool}, E.drop p = encodeList encodeNat as ++ rest → c ≤ B →
      a ≤ B → AHalt (scan .edge) o (X n w) (Gd B) (some (.aA true), rg p c a, none)
        (decide (iv ∈ as)) := by
  induction as with
  | nil =>
    intro p c a rest h hc ha
    have hl := le_of_drop h (by simp [encodeList])
    simp only [encodeList, List.length_singleton] at hl h
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    rw [astep_rd hrd _ _ _ rfl, getD_of_drop (by simpa using h)]
    simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, decide_false]
    exact AHalt.ret (by simp [scan]) (gd_rg (by omega) hc ha)
  | cons k as ih =>
    intro p c a rest h hc ha
    have hl := le_of_drop h (by simp [encodeList])
    rw [length_encodeList_cons] at hl
    simp only [encodeNat, List.length_append, List.length_replicate,
      List.length_singleton] at hl
    simp only [encodeList, encodeNat, List.cons_append, List.append_assoc] at h
    have h1 := drop_succ_of_drop h
    have hu := drop_add_of_drop (s := List.replicate k true ++ [false]) (by simpa using h1)
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hu
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    rw [astep_rd hrd _ _ _ rfl, getD_of_drop h]
    simp only [↓reduceIte]
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, rg_zero, upd_zero]
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, upd_two]
    refine (uloop hrd true h1 hB hc).halt ?_
    refine AHalt.step (gd_rg (by omega) hc (by omega)) ?_
    rw [astep_jeqFst ht]
    by_cases hk : k = iv
    · subst hk
      simp only [↓reduceIte, List.mem_cons, true_or, decide_true]
      exact AHalt.ret (by simp [scan]) (gd_rg (by omega) hc (by omega))
    · simp only [hk, ↓reduceIte, List.mem_cons, Ne.symm hk, false_or]
      refine AHalt.step (gd_rg (by omega) hc (by omega)) ?_
      simp only [astep, scan, rg_zero, upd_zero]
      have := ih (p := p + 1 + k + 1) (c := c) (a := k) (by rw [← hu]; congr 1) hc
        (by omega)
      exact this

/-- A gate's code is its two-bit label followed by the code of its argument list. -/
lemma length_gate_encode (g : DAGGate) :
    g.encode.length = 2 + (encodeList encodeNat g.args).length := by
  have : g.kind.encode.length = 2 := by cases g.kind <;> rfl
  simp [DAGGate.encode, this]

/-- **Skipping a gate.**

**Proof sketch.** Increment the vertex counter, skip the leading `1` and the two label bits,
then skip the argument list (`argsSkip`), which ends in `gA` right after the gate's code. -/
lemma gateSkip (hrd : ∀ p, o 0 (X n (Nat.bits p)) = E.getD p false) {B : ℕ}
    (hB : E.length ≤ B) (g : DAGGate) {p c a : ℕ} {rest : List Bool}
    (h : E.drop p = true :: (g.encode ++ rest)) (hc : c + 1 ≤ B) (ha : a ≤ B) :
    ∃ a' ≤ B, AReach (scan τ) o (X n w) (Gd B) (some .gC, rg p c a, none)
      (some .gA, rg (p + 1 + g.encode.length) (c + 1) a', none) := by
  have hl := le_of_drop (s := true :: g.encode) (rest := rest) (by simpa using h) (by simp)
  simp only [List.length_cons] at hl
  have hk : g.kind.encode.length = 2 := by cases g.kind <;> rfl
  have h3 : E.drop (p + 1 + 2) = encodeList encodeNat g.args ++ rest := by
    have := drop_add_of_drop (s := true :: g.kind.encode) (rest := encodeList encodeNat g.args ++ rest)
      (by simpa [DAGGate.encode] using h)
    simpa [hk] using this
  obtain ⟨a', ha', hr⟩ := argsSkip (τ := τ) (w := w) hrd hB g.args h3 (c := c + 1) (by omega) ha
  refine ⟨a', ha', ?_⟩
  rw [length_gate_encode] at hl ⊢
  refine AReach.step (gd_rg (by omega) (by omega) ha) ?_
  simp only [astep, scan, rg_one, upd_one]
  refine AReach.step (gd_rg (by omega) (by omega) ha) ?_
  simp only [astep, scan, rg_zero, upd_zero]
  refine AReach.step (gd_rg (by omega) (by omega) ha) ?_
  simp only [astep, scan, rg_zero, upd_zero]
  refine AReach.step (gd_rg (by omega) (by omega) ha) ?_
  simp only [astep, scan, rg_zero, upd_zero]
  convert hr using 4
  omega

/-- `decodeKind` inverts the two-bit label code. -/
lemma decodeKind_encode (k : GateKind) {b₁ b₂ : Bool} (h : k.encode = [b₁, b₂]) :
    decodeKind b₁ b₂ = k := by
  cases k <;> simp [GateKind.encode] at h <;> obtain ⟨rfl, rfl⟩ := h <;> rfl

/-- **The target gate**: the answer is `hitAns`.

**Proof sketch.** Case on the task. `SIZE` answers `true` at once. `TYPE t` reads the two label
bits and answers whether `t` is the decoded label (`decodeKind_encode`). `EDGE` skips the label
and examines the argument list (`argsEx`). -/
lemma hitGate {iv tv : ℕ} (hrd : ∀ p, o 0 (X n (Nat.bits p)) = E.getD p false)
    (ht : Target τ (X n w) iv tv) {B : ℕ} (hB : E.length ≤ B) (g : DAGGate) {p c a : ℕ}
    {rest : List Bool} (h : E.drop p = true :: (g.encode ++ rest)) (hc : c ≤ B) (ha : a ≤ B) :
    AHalt (scan τ) o (X n w) (Gd B) (some .hHit, rg p c a, none) (hitAns iv g τ) := by
  have hl := le_of_drop (s := true :: g.encode) (rest := rest) (by simpa using h) (by simp)
  simp only [List.length_cons] at hl
  rw [length_gate_encode] at hl
  obtain ⟨b₁, b₂, hk⟩ : ∃ b₁ b₂, g.kind.encode = [b₁, b₂] := by
    cases g.kind
    · exact ⟨false, false, rfl⟩
    · exact ⟨false, true, rfl⟩
    · exact ⟨true, false, rfl⟩
  have h' : E.drop p = [true, b₁, b₂] ++ (encodeList encodeNat g.args ++ rest) := by
    simpa [DAGGate.encode, hk] using h
  have hb₁ : E.getD (p + 1) false = b₁ := getD_of_drop (rest := b₂ :: (encodeList encodeNat g.args ++ rest))
    (by rw [← List.drop_drop, h']; rfl)
  have hb₂ : E.getD (p + 1 + 1) false = b₂ := getD_of_drop (rest := encodeList encodeNat g.args ++ rest)
    (by rw [← List.drop_drop, ← List.drop_drop, h']; rfl)
  have h3 : E.drop (p + 1 + 1 + 1) = encodeList encodeNat g.args ++ rest := by
    rw [← List.drop_drop, ← List.drop_drop, ← List.drop_drop, h']; rfl
  cases τ with
  | size => exact AHalt.ret rfl (gd_rg (by omega) hc ha)
  | type t =>
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, rg_zero, upd_zero]
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    rw [astep_rd hrd _ _ _ rfl, hb₁]
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    cases b₁ <;> simp only [astep, scan, rg_zero, upd_zero, Bool.false_eq_true,
      ↓reduceIte] <;>
    · refine AHalt.step (gd_rg (by omega) hc ha) ?_
      rw [astep_rd hrd _ _ _ rfl, hb₂]
      cases b₂ <;>
      · refine AHalt.ret ?_ (gd_rg (by omega) hc ha)
        simp only [scan, hitAns, ← decodeKind_encode g.kind hk, Bool.false_eq_true, ↓reduceIte]
  | edge =>
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, rg_zero, upd_zero]
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, rg_zero, upd_zero]
    refine AHalt.step (gd_rg (by omega) hc ha) ?_
    simp only [astep, scan, rg_zero, upd_zero]
    exact argsEx hrd ht hB g.args h3 hc ha

/-- **The gate loop**: from the start of the gate list `gs` with vertex counter `c ≤ tv`,
the answer is `hitAns` of the target gate, or `false` beyond the list.

**Proof sketch.** Induction on the gate list. At the list end the scanner rejects. At a gate it
reads the leading `1` and tests the vertex counter against the target (`astep_hit`). On a hit,
`hitGate` gives the answer; otherwise `gateSkip` moves to the next gate with the counter
incremented, and the target's index in the remaining list drops by one. -/
lemma gloop {iv tv : ℕ} (hrd : ∀ p, o 0 (X n (Nat.bits p)) = E.getD p false)
    (ht : Target τ (X n w) iv tv) {B : ℕ} (hB : E.length ≤ B) (gs : List DAGGate) :
    ∀ {p c a : ℕ} {rest : List Bool}, E.drop p = encodeList DAGGate.encode gs ++ rest →
      c ≤ tv → c + gs.length ≤ B → a ≤ B →
      AHalt (scan τ) o (X n w) (Gd B) (some .gA, rg p c a, none)
        (if h : tv - c < gs.length then hitAns iv gs[tv - c] τ else false) := by
  induction gs with
  | nil =>
    intro p c a rest h hct hc ha
    have hl := le_of_drop h (by simp [encodeList])
    simp only [encodeList, List.length_singleton] at hl h
    refine AHalt.step (gd_rg (by omega) (by simpa using hc) ha) ?_
    rw [astep_rd hrd _ _ _ rfl, getD_of_drop (by simpa using h)]
    simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.not_lt_zero,
      ↓reduceDIte]
    exact AHalt.ret rfl (gd_rg (by omega) (by simpa using hc) ha)
  | cons g gs ih =>
    intro p c a rest h hct hc ha
    simp only [List.length_cons] at hc
    have hl := le_of_drop h (by simp [encodeList])
    simp only [encodeList, List.cons_append, List.append_assoc] at h
    have h' : E.drop p = true :: (g.encode ++ (encodeList DAGGate.encode gs ++ rest)) := h
    have hn := drop_add_of_drop (s := true :: g.encode)
      (rest := encodeList DAGGate.encode gs ++ rest) (by simpa using h')
    simp only [List.length_cons] at hn
    refine AHalt.step (gd_rg (by omega) (by omega) ha) ?_
    rw [astep_rd hrd _ _ _ rfl, getD_of_drop h']
    simp only [↓reduceIte]
    refine AHalt.step (gd_rg (by omega) (by omega) ha) ?_
    rw [astep_hit ht _ _ _ rfl]
    by_cases hct' : c = tv
    · subst hct'
      simp only [↓reduceIte, Nat.sub_self, List.length_cons, Nat.zero_lt_succ, ↓reduceDIte,
        List.getElem_cons_zero]
      exact hitGate hrd ht hB g h' (by omega) ha
    · simp only [hct', ↓reduceIte]
      obtain ⟨a', ha', hr⟩ := gateSkip (τ := τ) (w := w) hrd hB g h' (c := c) (by omega) ha
      refine hr.halt ?_
      have e : tv - c = (tv - (c + 1)) + 1 := by omega
      have := ih (p := p + (g.encode.length + 1)) (c := c + 1) (a := a') hn (by omega)
        (by omega) ha'
      rw [e]
      simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ]
      convert this using 4
      omega

/-- **The input loop**: from vertex `j ≤ n` of the unary prefix, the answer is `nAns` if the
target is an input, and the continuation's answer otherwise.

**Proof sketch.** Induction on the number `n - j` of input vertices left. Each `1` of the prefix
`1ⁿ` is an input vertex: on a hit (`astep_hit`) the scanner answers `nAns`, otherwise it counts
the vertex and moves on. At the `0` it skips into the gate loop at vertex `n`, where the
continuation applies. -/
lemma nloop {iv tv : ℕ} (hrd : ∀ p, o 0 (X n (Nat.bits p)) = E.getD p false)
    (ht : Target τ (X n w) iv tv) {B : ℕ} (hB : E.length ≤ B) {rest : List Bool}
    (h : E.drop 0 = List.replicate n true ++ false :: rest) {ans : Bool}
    (hcont : n ≤ tv → AHalt (scan τ) o (X n w) (Gd B) (some .gA, rg (n + 1) n 0, none) ans) :
    ∀ j, j ≤ n → j ≤ tv →
      AHalt (scan τ) o (X n w) (Gd B) (some .nA, rg j j 0, none)
        (if tv < n then nAns τ else ans) := by
  have hl := le_of_drop (E := E) (p := 0) (s := List.replicate n true ++ [false])
    (rest := rest) (by rw [h]; simp) (by simp)
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hl
  have key : ∀ d j, j + d = n → j ≤ tv →
      AHalt (scan τ) o (X n w) (Gd B) (some .nA, rg j j 0, none)
        (if tv < n then nAns τ else ans) := by
    intro d
    induction d with
    | zero =>
      intro j hj hjt
      obtain rfl : j = n := by omega
      have hb := bit_rep h (j := j) le_rfl
      rw [Nat.zero_add] at hb
      refine AHalt.step (gd_rg (by omega) (by omega) (by omega)) ?_
      rw [astep_rd hrd _ _ _ rfl, hb]
      simp only [lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine AHalt.step (gd_rg (by omega) (by omega) (by omega)) ?_
      simp only [astep, scan, rg_zero, upd_zero]
      rw [if_neg (by omega)]
      exact hcont hjt
    | succ d ih =>
      intro j hj hjt
      have hb := bit_rep h (j := j) (by omega)
      rw [Nat.zero_add] at hb
      refine AHalt.step (gd_rg (by omega) (by omega) (by omega)) ?_
      rw [astep_rd hrd _ _ _ rfl, hb]
      simp only [show j < n from by omega, decide_true, ↓reduceIte]
      refine AHalt.step (gd_rg (by omega) (by omega) (by omega)) ?_
      rw [astep_hit ht _ _ _ rfl]
      by_cases hjt' : j = tv
      · subst hjt'
        simp only [↓reduceIte, show j < n from by omega]
        exact AHalt.ret rfl (gd_rg (by omega) (by omega) (by omega))
      · simp only [hjt', ↓reduceIte]
        refine AHalt.step (gd_rg (by omega) (by omega) (by omega)) ?_
        simp only [astep, scan, rg_one, upd_one]
        refine AHalt.step (gd_rg (by omega) (by omega) (by omega)) ?_
        simp only [astep, scan, rg_zero, upd_zero]
        exact ih (j + 1) (by omega) (by omega)
  intro j hj hjt
  exact key (n - j) j (by omega) hjt

end Loops

/-- The format check of task `τ`: `⟨1ⁿ, w⟩`, or `⟨1ⁿ, ⟨u, w⟩⟩` for `EDGE`. -/
def Valid (τ : Task) (x : List Bool) : Prop :=
  match τ with
  | .edge => ValidPair x
  | _ => ValidPlain x

/-- **The scanner's run** on a description `E = encode Cₙ`: it answers `nAns τ` if the target
vertex is an input, `hitAns` of the target gate if it is a gate, and `false` beyond the
circuit, with all registers at most `|E|`.

**Proof sketch.** The input loop (`nloop`) walks the unary prefix `1ⁿ0`, then the gate loop
(`gloop`) walks the gates, skipping each (`gateSkip`, `argsSkip`, `uloop`) until the target
gate, whose label or argument list is examined (`hitGate`, `argsEx`). -/
theorem scan_halts {τ : Task} {n : ℕ} (C : DAGCircuit n) {w : List Bool}
    {o : Fin 1 → List Bool → Bool} {iv tv : ℕ}
    (hrd : ∀ p, o 0 (X n (Nat.bits p)) = C.encode.getD p false)
    (ht : Target τ (X n w) iv tv) (hv : Valid τ (X n w)) :
    AHalt (scan τ) o (X n w) (Gd C.encode.length) (some .start, fun _ => 0, none)
      (if tv < n then nAns τ else
        if h : tv - n < C.gates.length then hitAns iv C.gates[tv - n] τ else false) := by
  set E := C.encode with hE
  have hsz := C.size_le_length_encode
  simp only [DAGCircuit.size] at hsz
  have h0 : E.drop 0 = List.replicate n true ++ false ::
      (encodeList DAGGate.encode C.gates ++ (List.replicate C.output true ++ [false])) := by
    rw [List.drop_zero, hE, C.encode_eq]
  have h1 : E.drop (n + 1) =
      encodeList DAGGate.encode C.gates ++ (List.replicate C.output true ++ [false]) := by
    have := drop_add_of_drop (E := E) (p := 0) (s := List.replicate n true ++ [false])
      (rest := encodeList DAGGate.encode C.gates ++ (List.replicate C.output true ++ [false]))
      (by rw [h0]; simp)
    simpa using this
  rw [rg_init]
  refine AHalt.step (gd_rg (by omega) (by omega) (by omega)) ?_
  have hst : astep (scan τ) o (X n w) (some .start, rg 0 0 0, none) =
      (some .nA, rg 0 0 0, none) := by
    cases τ <;> simp only [Valid] at hv <;> simp [astep, scan, hv]
  rw [hst]
  refine nloop hrd ht le_rfl h0 (fun hn => ?_) 0 (by omega) (by omega)
  have := gloop hrd ht le_rfl C.gates (p := n + 1) (c := n) (a := 0) h1 hn (by omega)
    (by omega)
  exact this

end AdjScan

end BoolCircuit
