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
# Writing a circuit description in logarithmic space

The "if" half of [AB09, p. 112]'s robustness remark: from `SIZE`, `TYPE` and `EDGE`, the
description `BoolCircuit.DAGCircuit.encode Cₙ` of a canonical circuit is produced by a walk
over the vertices and candidate arguments, emitting its bits in order. Bit `i` of the
description (and whether `i` is below its length) is decided by running the walk with an
emission counter and stopping at the `i`-th emitted bit.

The walk is the abstract register machine `BoolCircuit.AdjWalk.walk lm`; emissions are
tracked by `BoolCircuit.AdjWalk.Em`, which composes along concatenation of emitted words.

## Main definitions

* `BoolCircuit.AdjWalk.walk` — the walk (`lm = true`: answer whether the `i`-th bit exists;
  `lm = false`: answer the `i`-th bit).
* `BoolCircuit.AdjWalk.Em` — "this run emits `S` from counter value `k`".

## Main results

* `BoolCircuit.AdjWalk.walk_halts` — the walk's answer is bit `i` of the description (or
  whether it exists).

File size: about 700 lines, over the 600-line target. The file is one abstract machine
with the emission calculus and the run lemmas of its nested loops, which all rely on the
machine's definition. The language-level theorems are in
`TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdj`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.2.1, p. 112.)
-/

namespace BoolCircuit

namespace AdjWalk

open Turing Complexity LogProg

/-- The emission sites of the walk. -/
inductive Site where
  | inOne | inEnd | gOne | gEnd | kA1 | kA2 | kO1 | kO2 | kN1 | kN2
  | aOne | uOne | uEnd | aEnd | oOne | oEnd
  deriving DecidableEq, Fintype

/-- The labels of the walk. -/
inductive Lbl where
  | start | nI | incV | gS | kA | kB | aS | aL | aE | clrW | uL | incW | aN | incV2
  | oS | oI | oL | incWo | done
  | em (s : Site) | bump (s : Site) | hitL (b : Bool)
  deriving DecidableEq, Fintype

/-- The bit emitted at a site. -/
def Site.bit : Site → Bool
  | .inOne | .gOne | .kO2 | .kN1 | .aOne | .uOne | .oOne => true
  | _ => false

/-- Where the walk continues after an emission. -/
def Site.next : Site → Lbl
  | .inOne => .incV
  | .inEnd => .gS
  | .gOne => .kA
  | .gEnd => .oS
  | .kA1 => .em .kA2
  | .kA2 => .aS
  | .kO1 => .em .kO2
  | .kO2 => .aS
  | .kN1 => .em .kN2
  | .kN2 => .aS
  | .aOne => .clrW
  | .uOne => .incW
  | .uEnd => .aN
  | .aEnd => .incV2
  | .oOne => .incWo
  | .oEnd => .done

/-- The deciders called by the walk: `SIZE`, `TYPE none`, `TYPE ∧`, `TYPE ∨`, `EDGE`. -/
def decs (C : DAGCircuitFamily) : Fin 5 → Language Bool
  | 0 => C.sizeLang
  | 1 => C.typeLang none
  | 2 => C.typeLang (some .and)
  | 3 => C.typeLang (some .or)
  | 4 => C.edgeLang

/-- **The walk.** Registers: `0` the emission counter `k`, `1` the vertex `V`, `2` the
candidate argument `U`, `3` the unary counter `W`. Each emission compares `k` with the
target index `i` (the input's word): at `k = i` it answers, otherwise it increments `k`. -/
def walk (lm : Bool) : ARM 4 5 Lbl
  | .start => .valP 0 .nI
  | .nI => .call 1 .unaryFst [1] (.em .inOne) (.em .inEnd)
  | .incV => .inc 1 .nI
  | .gS => .call 0 .unaryFst [1] (.em .gOne) (.em .gEnd)
  | .kA => .call 2 .unaryFst [1] (.em .kA1) .kB
  | .kB => .call 3 .unaryFst [1] (.em .kO1) (.em .kN1)
  | .aS => .clr 2 .aL
  | .aL => .jeq 2 1 (.em .aEnd) .aE
  | .aE => .call 4 .unaryFst [2, 1] (.em .aOne) .aN
  | .clrW => .clr 3 .uL
  | .uL => .jeq 3 2 (.em .uEnd) (.em .uOne)
  | .incW => .inc 3 .uL
  | .aN => .inc 2 .aL
  | .incV2 => .inc 1 .gS
  | .oS => .clr 3 .oI
  | .oI => .inc 3 .oL
  | .oL => .jeq 3 1 (.em .oEnd) (.em .oOne)
  | .incWo => .inc 3 .oL
  | .done => .ret false
  | .em s => .jeqIn 0 (.hitL s.bit) (.bump s)
  | .bump s => .inc 0 s.next
  | .hitL b => .ret (lm || b)

/-! ## Registers -/

/-- The register file `(k, V, U, W)`. -/
def rg (k V U W : ℕ) : Fin 4 → ℕ := ![k, V, U, W]

/-- Register `0` of `rg k V U W` is the emission counter `k`. -/
@[simp] lemma rg_0 (k V U W : ℕ) : rg k V U W 0 = k := rfl
/-- Register `1` of `rg k V U W` is the vertex `V`. -/
@[simp] lemma rg_1 (k V U W : ℕ) : rg k V U W 1 = V := rfl
/-- Register `2` of `rg k V U W` is the candidate argument `U`. -/
@[simp] lemma rg_2 (k V U W : ℕ) : rg k V U W 2 = U := rfl
/-- Register `3` of `rg k V U W` is the unary counter `W`. -/
@[simp] lemma rg_3 (k V U W : ℕ) : rg k V U W 3 = W := rfl

/-- A property of all four registers follows from the property of each. -/
lemma fin4_cases {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ r, P r
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

/-- Setting register `0` of `rg k V U W` to `q` gives `rg q V U W`. -/
@[simp] lemma upd_0 (k V U W q : ℕ) : Function.update (rg k V U W) 0 q = rg q V U W := by
  funext r; revert r; refine fin4_cases ?_ ?_ ?_ ?_ <;> rfl
/-- Setting register `1` of `rg k V U W` to `q` gives `rg k q U W`. -/
@[simp] lemma upd_1 (k V U W q : ℕ) : Function.update (rg k V U W) 1 q = rg k q U W := by
  funext r; revert r; refine fin4_cases ?_ ?_ ?_ ?_ <;> rfl
/-- Setting register `2` of `rg k V U W` to `q` gives `rg k V q W`. -/
@[simp] lemma upd_2 (k V U W q : ℕ) : Function.update (rg k V U W) 2 q = rg k V q W := by
  funext r; revert r; refine fin4_cases ?_ ?_ ?_ ?_ <;> rfl
/-- Setting register `3` of `rg k V U W` to `q` gives `rg k V U q`. -/
@[simp] lemma upd_3 (k V U W q : ℕ) : Function.update (rg k V U W) 3 q = rg k V U q := by
  funext r; revert r; refine fin4_cases ?_ ?_ ?_ ?_ <;> rfl

/-- The all-zero register file is `rg 0 0 0 0`. -/
lemma rg_init : (fun _ : Fin 4 => 0) = rg 0 0 0 0 := by
  funext r; revert r; refine fin4_cases ?_ ?_ ?_ ?_ <;> rfl

/-- The guard: every register at most `B`. -/
def Gd (B : ℕ) (a : AConf 4 Lbl) : Prop := ∀ r, a.2.1 r ≤ B

/-- A configuration whose registers are all at most `B` satisfies the guard `Gd B`. -/
lemma gd_rg {B k V U W : ℕ} {l : Option Lbl} {res : Option Bool} (hk : k ≤ B) (hV : V ≤ B)
    (hU : U ≤ B) (hW : W ≤ B) : Gd B (l, rg k V U W, res) := by
  intro r; revert r; refine fin4_cases ?_ ?_ ?_ ?_ <;> simpa

/-! ## Emissions -/

section Em

variable (lm : Bool) (n i B : ℕ) (o : Fin 5 → List Bool → Bool)

/-- The input `⟨1ⁿ, bits i⟩`. -/
abbrev X : List Bool := pairEncode (List.replicate n true) (Nat.bits i)

/-- **Emission**: from `a`, with emission counter `k ≤ i`, the walk emits `S`: if the `i`-th
bit falls in `S` the walk answers it, and otherwise it reaches a configuration satisfying
`P`. -/
def Em (k : ℕ) (S : List Bool) (a : AConf 4 Lbl) (P : AConf 4 Lbl → Prop) : Prop :=
  (k ≤ i → i < k + S.length →
      AHalt (walk lm) o (X n i) (Gd B) a (lm || S.getD (i - k) false)) ∧
    (k + S.length ≤ i → ∃ b, P b ∧ AReach (walk lm) o (X n i) (Gd B) a b)

variable {lm n i B o}

/-- Emissions compose: emitting `S` and then, from every configuration reached, `T`, emits
`S ++ T`. -/
lemma Em.append {k : ℕ} {S T : List Bool} {a : AConf 4 Lbl} {P Q : AConf 4 Lbl → Prop}
    (h₁ : Em lm n i B o k S a P)
    (h₂ : k + S.length ≤ i → ∀ b, P b → Em lm n i B o (k + S.length) T b Q) :
    Em lm n i B o k (S ++ T) a Q := by
  constructor
  · intro hk hi
    rcases Nat.lt_or_ge i (k + S.length) with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]; exact h₁.1 hk h
    · obtain ⟨b, hb, hr⟩ := h₁.2 h
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have := (h₂ h b hb).1 h (by simp at hi; omega)
      rw [show i - k - S.length = i - (k + S.length) by omega]
      exact hr.halt this
  · intro hi
    simp only [List.length_append] at hi
    obtain ⟨b, hb, hr⟩ := h₁.2 (by omega)
    obtain ⟨c, hc, hr'⟩ := (h₂ (by omega) b hb).2 (by omega)
    exact ⟨c, hc, hr.trans hr'⟩

/-- A configuration satisfying `P` emits the empty word towards `P`. -/
lemma Em.nil {k : ℕ} {a : AConf 4 Lbl} {P : AConf 4 Lbl → Prop} (h : P a) :
    Em lm n i B o k [] a P :=
  ⟨fun _ hi => absurd hi (by simp; omega), fun _ => ⟨a, h, AReach.refl _⟩⟩

/-- A non-emitting run may precede an emission. -/
lemma Em.pre {k : ℕ} {S : List Bool} {a b : AConf 4 Lbl} {P : AConf 4 Lbl → Prop}
    (hr : AReach (walk lm) o (X n i) (Gd B) a b) (h : Em lm n i B o k S b P) :
    Em lm n i B o k S a P :=
  ⟨fun hk hi => hr.halt (h.1 hk hi), fun hi => by
    obtain ⟨c, hc, hr'⟩ := h.2 hi
    exact ⟨c, hc, hr.trans hr'⟩⟩

/-- A non-emitting step may precede an emission. -/
lemma Em.step {k : ℕ} {S : List Bool} {a : AConf 4 Lbl} {P : AConf 4 Lbl → Prop}
    (hG : Gd B a) (h : Em lm n i B o k S (astep (walk lm) o (X n i) a) P) :
    Em lm n i B o k S a P :=
  Em.pre (AReach.single hG) h

/-- An emission towards `P` is an emission towards any weaker `Q`. -/
lemma Em.mono {k : ℕ} {S : List Bool} {a : AConf 4 Lbl} {P Q : AConf 4 Lbl → Prop}
    (h : Em lm n i B o k S a P) (hPQ : ∀ b, P b → Q b) : Em lm n i B o k S a Q :=
  ⟨h.1, fun hi => by
    obtain ⟨c, hc, hr⟩ := h.2 hi
    exact ⟨c, hPQ c hc, hr⟩⟩

/-- Continue a run after an emission. -/
lemma Em.cont {k : ℕ} {S : List Bool} {a : AConf 4 Lbl} {P Q : AConf 4 Lbl → Prop}
    (h : Em lm n i B o k S a P)
    (h₂ : k + S.length ≤ i → ∀ b, P b → ∃ c, Q c ∧ AReach (walk lm) o (X n i) (Gd B) b c) :
    Em lm n i B o k S a Q :=
  ⟨h.1, fun hi => by
    obtain ⟨b, hb, hr⟩ := h.2 hi
    obtain ⟨c, hc, hr'⟩ := h₂ hi b hb
    exact ⟨c, hc, hr.trans hr'⟩⟩

/-- **One emission** at site `s`: from `em s` with emission counter `k`, the walk answers the site's
bit if `k = i`, and otherwise increments `k` and continues at the site's successor.

**Proof sketch.** The emission is a `jeqIn` on the counter, which compares `bits k` with the
input's word `bits i` (`plainWord_pairEncode`, `bits_injective`). On equality it moves to `hitL
s.bit` and returns `lm || s.bit`. Otherwise it moves to `bump s`, which increments the counter
and jumps to `s.next`. -/
lemma Em.emit (s : Site) {k V U W : ℕ} (hk : k ≤ i) (hB : k + 1 ≤ B) (hV : V ≤ B) (hU : U ≤ B)
    (hW : W ≤ B) :
    Em lm n i B o k [s.bit] (some (.em s), rg k V U W, none)
      (· = (some s.next, rg (k + 1) V U W, none)) := by
  have hstep : astep (walk lm) o (X n i) (some (.em s), rg k V U W, none) =
      (some (if k = i then .hitL s.bit else .bump s), rg k V U W, none) := by
    simp [astep, walk, plainWord_pairEncode, bits_injective.eq_iff]
  constructor
  · intro _ hi
    obtain rfl : k = i := by simp at hi; omega
    refine AHalt.step (gd_rg (by omega) hV hU hW) ?_
    rw [hstep]
    simp only [↓reduceIte, Nat.sub_self, List.getD_cons_zero]
    exact AHalt.ret rfl (gd_rg (by omega) hV hU hW)
  · intro hi
    simp only [List.length_singleton] at hi
    refine ⟨_, rfl, AReach.step (gd_rg (by omega) hV hU hW) ?_⟩
    rw [hstep, if_neg (by omega)]
    refine AReach.step (gd_rg (by omega) hV hU hW) ?_
    simp only [astep, walk, rg_0, upd_0]
    exact AReach.refl _

end Em

/-! ## Calls -/

/-- The oracle: the deciders' languages. -/
noncomputable def orc (C : DAGCircuitFamily) : Fin 5 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (decs C j : Set (List Bool)) V

section Calls

variable {lm : Bool} {n i : ℕ} {o : Fin 5 → List Bool → Bool}

/-- A `unaryFst` call with one argument `r` asks its decider about `⟨1ⁿ, bits (v r)⟩`. -/
lemma astep_call₁ {l l₁ l₀ : Lbl} {j : Fin 5} {r : Fin 4}
    (hl : walk lm l = .call j .unaryFst [r] l₁ l₀) (v : Fin 4 → ℕ) :
    astep (walk lm) o (X n i) (some l, v, none) =
      (some (if o j (pairEncode (List.replicate n true) (Nat.bits (v r))) then l₁ else l₀),
        v, none) := by
  simp only [astep, hl]
  rw [vword_unary₁]

/-- A `unaryFst` call with arguments `r, r'` asks its decider about
`⟨1ⁿ, ⟨bits (v r), bits (v r')⟩⟩`. -/
lemma astep_call₂ {l l₁ l₀ : Lbl} {j : Fin 5} {r r' : Fin 4}
    (hl : walk lm l = .call j .unaryFst [r, r'] l₁ l₀) (v : Fin 4 → ℕ) :
    astep (walk lm) o (X n i) (some l, v, none) =
      (some (if o j (pairEncode (List.replicate n true)
        (pairEncode (Nat.bits (v r)) (Nat.bits (v r')))) then l₁ else l₀), v, none) := by
  simp only [astep, hl]
  rw [vword_unary₂]

variable (C : DAGCircuitFamily)

open Classical in
/-- The `SIZE` decider answers whether `v` is a vertex of `Cₙ`. -/
lemma orc_size (v : ℕ) : orc C 0 (pairEncode (List.replicate n true) (Nat.bits v)) =
    decide (v < (C.circuit n).size) := by
  simp only [orc, decs, indicator_eq_decide]
  exact decide_eq_decide.mpr C.mem_sizeLang

open Classical in
/-- A `TYPE t` decider answers whether `v` is a vertex of `Cₙ` of type `t`. -/
lemma orc_type (j : Fin 5) (t : Option GateKind) (hj : decs C j = C.typeLang t) (v : ℕ) :
    orc C j (pairEncode (List.replicate n true) (Nat.bits v)) =
      decide (v < (C.circuit n).size ∧ (C.circuit n).vtype v = t) := by
  simp only [orc, hj, indicator_eq_decide]
  exact decide_eq_decide.mpr C.mem_typeLang

open Classical in
/-- The `EDGE` decider answers whether `u → v` is an edge of `Cₙ`. -/
lemma orc_edge (u v : ℕ) :
    orc C 4 (pairEncode (List.replicate n true) (pairEncode (Nat.bits u) (Nat.bits v))) =
      decide ((C.circuit n).Edge u v) := by
  simp only [orc, decs, indicator_eq_decide]
  exact decide_eq_decide.mpr C.mem_edgeLang

end Calls

/-! ## The loops -/

section Loops

variable {lm : Bool} {n i B : ℕ} (C : DAGCircuitFamily)

/-- **The unary loop** emits `1^{U - W} 0`.

**Proof sketch.** Induction on the number `d` of `1`s left. While `W ≠ U` the walk emits `1`
(`Em.emit`) and increments `W`; at `W = U` it emits `0` and moves to `aN`. Emissions compose by
`Em.append`. -/
lemma uLoop {V U : ℕ} (hV : V ≤ B) (hU : U ≤ B) :
    ∀ d W k, W + d = U → k ≤ i → k + d + 1 ≤ B →
      Em lm n i B (orc C) k (List.replicate d true ++ [false]) (some .uL, rg k V U W, none)
        (· = (some .aN, rg (k + d + 1) V U U, none)) := by
  intro d
  induction d with
  | zero =>
    intro W k hW hk hkB
    obtain rfl : W = U := by omega
    refine Em.step (gd_rg (by omega) hV hU hU) ?_
    simp only [astep, walk, rg_2, rg_3, ↓reduceIte]
    exact (Em.emit .uEnd hk (by omega) hV hU hU).mono fun b hb => by rw [hb]; rfl
  | succ d ih =>
    intro W k hW hk hkB
    refine Em.step (gd_rg (by omega) hV hU (by omega)) ?_
    simp only [astep, walk, rg_2, rg_3, show W ≠ U by omega, ↓reduceIte]
    rw [List.replicate_succ, List.cons_append]
    refine Em.append (S := [Site.uOne.bit]) (Em.emit .uOne hk (by omega) hV hU (by omega))
      (fun hki b hb => ?_)
    subst hb
    simp only [Site.next, List.length_singleton] at hki ⊢
    refine Em.step (gd_rg (by omega) hV hU (by omega)) ?_
    simp only [astep, walk, rg_3, upd_3]
    exact (ih (W + 1) (k + 1) (by omega) hki (by omega)).mono fun b hb => by
      rw [hb]; congr 3; omega

/-- For a gate `g` at vertex `V`, `U → V` is an edge iff `U` is an argument of `g`. -/
lemma edge_iff {V U : ℕ} {g : DAGGate} (hg : (C.circuit n).gates[V - n]? = some g)
    (hnV : n ≤ V) : (C.circuit n).Edge U V ↔ U ∈ g.args := by
  simp [DAGCircuit.Edge, hg, hnV]

/-- **The argument loop** of the gate `g` at vertex `V`: from candidate `U`, it emits the
arguments in `[U, V)` and the list end.

**Proof sketch.** Induction on the number `d` of candidates left. At `U = V` the walk emits the
list end `0` and moves to the next vertex. Otherwise it asks `EDGE(U, V)`, which is `U ∈ g.args`
(`edge_iff`). If so, it emits `1`, then `1ᵁ0` via the unary loop (`uLoop`); in both cases it
moves on to `U + 1`, matching the filtered range. -/
lemma aLoop {V : ℕ} (g : DAGGate) (hg : (C.circuit n).gates[V - n]? = some g) (hnV : n ≤ V)
    (hVB : V + 1 ≤ B) :
    ∀ d U k W K, U + d = V → k ≤ i → W ≤ B →
      K = k + (encodeList encodeNat ((List.range' U d).filter (· ∈ g.args))).length → K ≤ B →
      Em lm n i B (orc C) k (encodeList encodeNat ((List.range' U d).filter (· ∈ g.args)))
        (some .aL, rg k V U W, none)
        (fun b => ∃ W' ≤ B, b = (some .gS, rg K (V + 1) V W', none)) := by
  intro d
  induction d with
  | zero =>
    intro U k W K hU hk hW hK hKB
    obtain rfl : U = V := by omega
    simp only [List.range'_zero, List.filter_nil, encodeList, List.length_singleton] at hK ⊢
    refine Em.step (gd_rg (by omega) (by omega) (by omega) hW) ?_
    simp only [astep, walk, rg_1, rg_2, ↓reduceIte]
    refine (Em.emit .aEnd hk (by omega) (by omega) (by omega) hW).cont fun _ b hb => ?_
    subst hb
    refine ⟨_, ⟨W, hW, rfl⟩, AReach.step (gd_rg (by omega) (by omega) (by omega) hW) ?_⟩
    simp only [Site.next, astep, walk, rg_1, upd_1, hK]
    exact AReach.refl _
  | succ d ih =>
    intro U k W K hU hk hW hK hKB
    rw [List.range'_succ, List.filter_cons] at hK ⊢
    refine Em.step (gd_rg (by omega) (by omega) (by omega) hW) ?_
    simp only [astep, walk, rg_1, rg_2, show U ≠ V by omega, ↓reduceIte]
    refine Em.step (gd_rg (by omega) (by omega) (by omega) hW) ?_
    rw [astep_call₂ rfl, rg_2, rg_1, orc_edge]
    by_cases he : U ∈ g.args
    · have hE : (C.circuit n).Edge U V := (edge_iff C hg hnV).mpr he
      simp only [hE, decide_true, ↓reduceIte]
      simp only [he, decide_true, ↓reduceIte, encodeList, List.length_cons, List.length_append,
        encodeNat, List.length_replicate] at hK ⊢
      rw [show true :: (List.replicate U true ++ [false] ++
          encodeList encodeNat (List.filter (fun x => decide (x ∈ g.args)) (List.range' (U + 1) d)))
          = [Site.aOne.bit] ++ ((List.replicate U true ++ [false]) ++
          encodeList encodeNat (List.filter (fun x => decide (x ∈ g.args)) (List.range' (U + 1) d)))
          from rfl]
      refine Em.append (Em.emit .aOne hk (by omega) (by omega) (by omega) hW)
        (fun hki b hb => ?_)
      subst hb
      simp only [Site.next, List.length_singleton] at hki ⊢
      refine Em.step (gd_rg (by omega) (by omega) (by omega) hW) ?_
      simp only [astep, walk, upd_3]
      refine Em.append (uLoop C (by omega) (by omega) U 0 (k + 1) (by omega) hki (by omega))
        (fun hki' b hb => ?_)
      subst hb
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hki' ⊢
      refine Em.step (gd_rg (by omega) (by omega) (by omega) (by omega)) ?_
      simp only [astep, walk, rg_2, upd_2]
      refine (ih (U + 1) (k + 1 + (U + 1)) U K (by omega) hki' (by omega) ?_ hKB).mono
        fun b hb => hb
      rw [hK]; simp only [List.length_nil]; omega
    · have hne : ¬ (C.circuit n).Edge U V := fun h => he ((edge_iff C hg hnV).mp h)
      simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte, he] at hK ⊢
      refine Em.step (gd_rg (by omega) (by omega) (by omega) hW) ?_
      simp only [astep, walk, rg_2, upd_2]
      exact ih (U + 1) k W K (by omega) hk hW hK hKB

/-- The arguments of a canonical gate are the candidates below its vertex that are
arguments, in increasing order. -/
lemma args_eq_filter {g : DAGGate} {V : ℕ} (hs : g.args.Sorted (· < ·))
    (hlt : ∀ a ∈ g.args, a < V) : (List.range' 0 V).filter (· ∈ g.args) = g.args := by
  apply List.eq_of_perm_of_sorted (r := (· < ·))
  · rw [List.perm_ext_iff_of_nodup ((List.nodup_range' ..).filter _) hs.nodup]
    intro a
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨⟨by omega, by simpa using hlt a h⟩, h⟩⟩
  · exact (List.sorted_lt_range' 0 V (by omega)).filter _
  · exact hs

/-- For a gate `g` at vertex `V`, `V` is a vertex of type `t` iff `t` is `g`'s label. -/
lemma vtype_gate {V : ℕ} {g : DAGGate} (hg : (C.circuit n).gates[V - n]? = some g)
    (hnV : n ≤ V) (t : Option GateKind) :
    (V < (C.circuit n).size ∧ (C.circuit n).vtype V = t) ↔ some g.kind = t := by
  have hlt : V - n < (C.circuit n).gates.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  simp only [DAGCircuit.size, DAGCircuit.vtype, show ¬ V < n by omega, ↓reduceIte, hg,
    Option.map_some]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-- **The label** of the gate `g` at vertex `V`.

**Proof sketch.** Ask `TYPE ∧` and then `TYPE ∨` about `V` (`orc_type`, `vtype_gate`). The
answers determine the label `∧`, `∨` or `¬`, and the walk emits its two-bit code with two
emissions. -/
lemma kindEm {V : ℕ} (g : DAGGate) (hg : (C.circuit n).gates[V - n]? = some g) (hnV : n ≤ V)
    (hVB : V ≤ B) {k U W : ℕ} (hk : k ≤ i) (hkB : k + 2 ≤ B) (hU : U ≤ B) (hW : W ≤ B) :
    Em lm n i B (orc C) k g.kind.encode (some .kA, rg k V U W, none)
      (· = (some .aS, rg (k + 2) V U W, none)) := by
  have hT := fun t => vtype_gate C hg hnV t
  refine Em.step (gd_rg (by omega) hVB hU hW) ?_
  rw [astep_call₁ rfl, rg_1, orc_type C 2 (some .and) rfl]
  cases hkd : g.kind with
  | and =>
    simp only [(hT _).mpr (by rw [hkd])]
    refine Em.append (S := [Site.kA1.bit]) (Em.emit .kA1 hk (by omega) hVB hU hW)
      fun hki b hb => ?_
    subst hb
    exact (Em.emit .kA2 hki (by simp; omega) hVB hU hW).mono fun b hb => by rw [hb]; rfl
  | or =>
    simp only [show ¬ (V < (C.circuit n).size ∧ (C.circuit n).vtype V = some .and) by
      rw [hT, hkd]; simp, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine Em.step (gd_rg (by omega) hVB hU hW) ?_
    rw [astep_call₁ rfl, rg_1, orc_type C 3 (some .or) rfl]
    simp only [(hT _).mpr (by rw [hkd])]
    refine Em.append (S := [Site.kO1.bit]) (Em.emit .kO1 hk (by omega) hVB hU hW)
      fun hki b hb => ?_
    subst hb
    exact (Em.emit .kO2 hki (by simp; omega) hVB hU hW).mono fun b hb => by rw [hb]; rfl
  | not =>
    simp only [show ¬ (V < (C.circuit n).size ∧ (C.circuit n).vtype V = some .and) by
      rw [hT, hkd]; simp, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine Em.step (gd_rg (by omega) hVB hU hW) ?_
    rw [astep_call₁ rfl, rg_1, orc_type C 3 (some .or) rfl]
    simp only [show ¬ (V < (C.circuit n).size ∧ (C.circuit n).vtype V = some .or) by
      rw [hT, hkd]; simp, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine Em.append (S := [Site.kN1.bit]) (Em.emit .kN1 hk (by omega) hVB hU hW)
      fun hki b hb => ?_
    subst hb
    exact (Em.emit .kN2 hki (by simp; omega) hVB hU hW).mono fun b hb => by rw [hb]; rfl

/-- **The gate loop**: from vertex `V ≥ n`, it emits the gates from `V` on and the list
end.

**Proof sketch.** Induction on the number of gates left. At `V = |Cₙ|`, `SIZE` says no and the
walk emits the list end `0`. Otherwise it emits `1`, the label (`kindEm`) and the argument list
(`aLoop` from `U = 0`), then moves to `V + 1`. For a canonical gate the candidates `< V` with an
edge to `V`, in increasing order, are exactly its arguments (`args_eq_filter`), so this is the
gate's code. -/
lemma gLoop (hcan : (C.circuit n).IsCanonical) (hSB : (C.circuit n).size + 1 ≤ B) :
    ∀ d V k U W K, V + d = (C.circuit n).size → n ≤ V → k ≤ i → U ≤ B → W ≤ B →
      K = k + (encodeList DAGGate.encode ((C.circuit n).gates.drop (V - n))).length → K ≤ B →
      Em lm n i B (orc C) k (encodeList DAGGate.encode ((C.circuit n).gates.drop (V - n)))
        (some .gS, rg k V U W, none)
        (fun b => ∃ U' ≤ B, ∃ W' ≤ B, b = (some .oS, rg K (C.circuit n).size U' W', none)) := by
  intro d
  induction d with
  | zero =>
    intro V k U W K hV hnV hk hU hW hK hKB
    have hd : (C.circuit n).gates.drop (V - n) = [] :=
      List.drop_of_length_le (by simp only [DAGCircuit.size] at hV; omega)
    rw [hd] at hK ⊢
    simp only [encodeList, List.length_singleton] at hK ⊢
    refine Em.step (gd_rg (by omega) (by omega) hU hW) ?_
    rw [astep_call₁ rfl, rg_1, orc_size]
    simp only [show ¬ V < (C.circuit n).size by omega, decide_false, Bool.false_eq_true,
      ↓reduceIte]
    exact (Em.emit .gEnd hk (by omega) (by omega) hU hW).mono fun b hb =>
      ⟨U, hU, W, hW, by rw [hb, hK, ← hV]; rfl⟩
  | succ d ih =>
    intro V k U W K hV hnV hk hU hW hK hKB
    have hlt : V - n < (C.circuit n).gates.length := by
      simp only [DAGCircuit.size] at hV; omega
    set g := (C.circuit n).gates[V - n] with hgdef
    have hg : (C.circuit n).gates[V - n]? = some g := List.getElem?_eq_getElem hlt
    have hd : (C.circuit n).gates.drop (V - n) = g :: (C.circuit n).gates.drop (V + 1 - n) := by
      rw [List.drop_eq_getElem_cons hlt]; congr 2; omega
    have hargs : (List.range' 0 V).filter (· ∈ g.args) = g.args :=
      args_eq_filter (hcan.1 g (List.getElem_mem hlt)) fun a ha => by
        have := (C.circuit n).args_lt (V - n) hlt a ha; omega
    have hS : encodeList DAGGate.encode ((C.circuit n).gates.drop (V - n)) =
        [Site.gOne.bit] ++ (g.kind.encode ++
          (encodeList encodeNat ((List.range' 0 V).filter (· ∈ g.args)) ++
            encodeList DAGGate.encode ((C.circuit n).gates.drop (V + 1 - n)))) := by
      rw [hd, hargs]; simp [encodeList, DAGGate.encode, Site.bit]
    have hkl : g.kind.encode.length = 2 := by cases g.kind <;> rfl
    rw [hS] at hK ⊢
    simp only [List.length_append, List.length_singleton, hkl] at hK
    refine Em.step (gd_rg (by omega) (by omega) hU hW) ?_
    rw [astep_call₁ rfl, rg_1, orc_size]
    simp only [show V < (C.circuit n).size by omega, decide_true, ↓reduceIte]
    refine Em.append (Em.emit .gOne hk (by omega) (by omega) hU hW) fun hki b hb => ?_
    subst hb
    simp only [Site.next, List.length_singleton] at hki ⊢
    refine Em.append (kindEm C g hg hnV (by omega) hki (by omega) hU hW) fun hki' b hb => ?_
    subst hb
    rw [hkl] at hki' ⊢
    refine Em.step (gd_rg (by omega) (by omega) hU hW) ?_
    simp only [astep, walk, upd_2]
    refine Em.append (aLoop C g hg hnV (by omega) V 0 (k + 1 + 2) W _ (by omega) hki' hW rfl
      (by omega)) fun hki'' b hb => ?_
    obtain ⟨W', hW', rfl⟩ := hb
    refine (ih (V + 1) _ V W' K (by omega) (by omega) hki'' (by omega) hW' ?_ hKB).mono
      fun b hb => hb
    rw [hK]; omega

/-- A vertex `V ≤ n` is a vertex of input type iff `V < n`. -/
lemma vtype_none {V : ℕ} (hV : V ≤ n) :
    (V < (C.circuit n).size ∧ (C.circuit n).vtype V = none) ↔ V < n := by
  simp only [DAGCircuit.size, DAGCircuit.vtype]
  rcases Nat.lt_or_ge V n with h | h
  · simp only [h, ↓reduceIte, and_true, iff_true]; omega
  · obtain rfl : V = n := by omega
    simp only [lt_self_iff_false, ↓reduceIte, Nat.sub_self, iff_false, not_and]
    intro hl
    rw [List.getElem?_eq_getElem (by omega)]
    simp

/-- **The input loop** emits `1^{n - V} 0`.

**Proof sketch.** Induction on the number `n - V` of inputs left. `TYPE none` says yes exactly
for `V < n` (`vtype_none`): then the walk emits `1` and increments `V`; at `V = n` it emits `0`
and moves to the gate loop. -/
lemma inLoop (hnB : n + 1 ≤ B) :
    ∀ d V k U W, V + d = n → k ≤ i → U ≤ B → W ≤ B → k + d + 1 ≤ B →
      Em lm n i B (orc C) k (List.replicate d true ++ [false]) (some .nI, rg k V U W, none)
        (· = (some .gS, rg (k + d + 1) n U W, none)) := by
  intro d
  induction d with
  | zero =>
    intro V k U W hV hk hU hW hkB
    obtain rfl : V = n := by omega
    refine Em.step (gd_rg (by omega) (by omega) hU hW) ?_
    rw [astep_call₁ rfl, rg_1, orc_type C 1 none rfl]
    simp only [(vtype_none C le_rfl).not.mpr (lt_irrefl _), decide_false,
      Bool.false_eq_true, ↓reduceIte]
    exact (Em.emit .inEnd hk (by omega) (by omega) hU hW).mono fun b hb => by rw [hb]; rfl
  | succ d ih =>
    intro V k U W hV hk hU hW hkB
    refine Em.step (gd_rg (by omega) (by omega) hU hW) ?_
    rw [astep_call₁ rfl, rg_1, orc_type C 1 none rfl]
    simp only [(vtype_none C (by omega)).mpr (by omega : V < n)]
    rw [List.replicate_succ, List.cons_append]
    refine Em.append (S := [Site.inOne.bit]) (Em.emit .inOne hk (by omega) (by omega) hU hW)
      fun hki b hb => ?_
    subst hb
    simp only [Site.next, List.length_singleton] at hki ⊢
    refine Em.step (gd_rg (by omega) (by omega) hU hW) ?_
    simp only [astep, walk, rg_1, upd_1]
    exact (ih (V + 1) (k + 1) U W (by omega) hki hU hW (by omega)).mono fun b hb => by
      rw [hb]; congr 3; omega

/-- **The output loop** emits `1^{V - W} 0`.

**Proof sketch.** Induction on the number `V - W` of `1`s left: while `W ≠ V` the walk emits `1`
and increments `W`; at `W = V` it emits `0` and moves to `done`. -/
lemma oLoop {V : ℕ} (hVB : V ≤ B) :
    ∀ d W k U, W + d = V → k ≤ i → U ≤ B → k + d + 1 ≤ B →
      Em lm n i B (orc C) k (List.replicate d true ++ [false]) (some .oL, rg k V U W, none)
        (· = (some .done, rg (k + d + 1) V U V, none)) := by
  intro d
  induction d with
  | zero =>
    intro W k U hW hk hU hkB
    obtain rfl : W = V := by omega
    refine Em.step (gd_rg (by omega) hVB hU hVB) ?_
    simp only [astep, walk, rg_1, rg_3, ↓reduceIte]
    exact (Em.emit .oEnd hk (by omega) hVB hU hVB).mono fun b hb => by rw [hb]; rfl
  | succ d ih =>
    intro W k U hW hk hU hkB
    refine Em.step (gd_rg (by omega) hVB hU (by omega)) ?_
    simp only [astep, walk, rg_1, rg_3, show W ≠ V by omega, ↓reduceIte]
    rw [List.replicate_succ, List.cons_append]
    refine Em.append (S := [Site.oOne.bit]) (Em.emit .oOne hk (by omega) hVB hU (by omega))
      fun hki b hb => ?_
    subst hb
    simp only [Site.next, List.length_singleton] at hki ⊢
    refine Em.step (gd_rg (by omega) hVB hU (by omega)) ?_
    simp only [astep, walk, rg_3, upd_3]
    exact (ih (W + 1) (k + 1) U (by omega) hki hU (by omega)).mono fun b hb => by
      rw [hb]; congr 3; omega

end Loops

/-- **The walk's run** on `⟨1ⁿ, bits i⟩` for a canonical `Cₙ`, with the deciders answering
`SIZE`, `TYPE`, `EDGE`: it answers `lm || E[i]` if `i < |E|` and `false` otherwise, where
`E = encode Cₙ`, with all registers at most `|E|`.

**Proof sketch.** The emissions compose (`Em.append`): the input loop emits `1ⁿ0`
(`inLoop`), the gate loop emits the gate list (`gLoop`: per gate a `1`, the label
(`kindEm`), the argument list (`aLoop`, `uLoop`), the arguments being the candidates
`U < V` with an edge `U → V` in increasing order since the circuit is canonical), and the
output loop emits `1^{|Cₙ| - 1}0`, the output being the last vertex (`oLoop`). -/
theorem walk_halts (C : DAGCircuitFamily) {n : ℕ} (hcan : (C.circuit n).IsCanonical)
    (lm : Bool) (i : ℕ) :
    AHalt (walk lm) (orc C) (X n i) (Gd (C.circuit n).encode.length)
      (some .start, fun _ => 0, none)
      (if i < (C.circuit n).encode.length then lm || (C.circuit n).encode.getD i false
        else false) := by
  set B := (C.circuit n).encode.length with hB
  have hlen := length_encodeList_ge DAGGate.encode (C.circuit n).gates
  have hE : (C.circuit n).encode = (List.replicate n true ++ [false]) ++
      (encodeList DAGGate.encode (C.circuit n).gates ++ (List.replicate ((C.circuit n).size - 1) true ++ [false])) := by
    rw [(C.circuit n).encode_eq, show (C.circuit n).output = (C.circuit n).size - 1 by have := hcan.2; omega]; simp
  have hBv : B = n + 1 + ((encodeList DAGGate.encode (C.circuit n).gates).length + ((C.circuit n).size - 1 + 1)) := by
    rw [hB, hE]; simp; omega
  have hS1 : 1 ≤ (C.circuit n).size := by have := hcan.2; omega
  have hSB : (C.circuit n).size + 1 ≤ B := by simp only [DAGCircuit.size] at hS1 ⊢; omega
  have hEm : Em lm n i B (orc C) 0 (C.circuit n).encode (some .nI, rg 0 0 0 0, none)
      (fun b => ∃ U ≤ B, b = (some .done, rg B (C.circuit n).size U (C.circuit n).size, none)) := by
    rw [hE]
    refine Em.append (inLoop C (by omega) n 0 0 0 0 (by omega) (Nat.zero_le _) (by omega)
      (by omega) (by omega)) fun hki b hb => ?_
    subst hb
    simp only [List.length_append, List.length_replicate, List.length_singleton,
      Nat.zero_add] at hki ⊢
    have hg := gLoop (lm := lm) C hcan hSB ((C.circuit n).size - n) n (n + 1) 0 0 _ (by simp [DAGCircuit.size])
      le_rfl hki (by omega) (by omega) rfl (by simp only [Nat.sub_self, List.drop_zero]; omega)
    simp only [Nat.sub_self, List.drop_zero] at hg
    refine Em.append hg fun hki' b hb => ?_
    obtain ⟨U', hU', W', hW', rfl⟩ := hb
    refine Em.step (gd_rg (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [astep, walk, upd_3]
    refine Em.step (gd_rg (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [astep, walk, rg_3, upd_3]
    refine (oLoop C (by omega) ((C.circuit n).size - 1) 1 _ U' (by omega) hki' (by omega) (by omega)).mono
      fun b hb => ⟨U', hU', by rw [hb]; congr 3; omega⟩
  rw [rg_init]
  refine AHalt.step (gd_rg (by omega) (by omega) (by omega) (by omega)) ?_
  have hv : ValidPlain (X n i) := ⟨n, _, rfl, canon_bits i⟩
  simp only [astep, walk, hv, ↓reduceIte]
  by_cases hi : i < B
  · rw [if_pos hi]
    simpa using hEm.1 (Nat.zero_le _) (by simpa using hi)
  · rw [if_neg hi]
    obtain ⟨b, ⟨U, hU, rfl⟩, hr⟩ := hEm.2 (by simp; omega)
    exact hr.halt (AHalt.ret rfl (gd_rg le_rfl (by omega) hU (by omega)))

end AdjWalk

end BoolCircuit
