/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.FanOut

/-!
# Strict circuits: [AB09, Def 6.1] taken literally

The library's circuit model `BoolCircuit.DAGCircuit` with `IsFaninTwo` relaxes
[AB09, Def 6.1] (see `DAGCircuit.lean`).  An `∧`/`∨` gate may have fan-in `0` (a
constant) or `1` (the identity), and vertices from which the output is unreachable are
allowed.  This file defines the literal model, shows it is empty at `n = 0`, and builds the
first half of the strictification: removing constants and identity gates.  The second
half and the consequences for `SIZE` and `P/poly` are in `StrictSize.lean`; fan-out two in
the literal model is in `StrictFanOut.lean`.

**Def 6.1 literally.**  A circuit is a DAG with `n` sources and *one sink*.  Its non-source
vertices are gates: `∧`/`∨` of fan-in exactly `2` and `¬` of fan-in exactly `1`.
`BoolCircuit.DAGCircuit.IsStrict` requires three things:
every `∧`/`∨` gate reads exactly two distinct vertices, every `¬` gate exactly one, and
every vertex other than the output has fan-out at least one.  Every gate then has fan-in
at least one, so no gate is a source and the sources are exactly the `n` inputs.  The
output is the only sink (`DAGCircuit.IsStrict.fanout_eq_zero_iff`).  In particular
*every input must be read*, since an unread input would be a second sink.  The book's
definition does force this, also for functions that ignore some input; strictification
reads such inputs harmlessly.

## Main definitions

* `BoolCircuit.DAGGate.Strict` — a gate of the literal model.
* `BoolCircuit.DAGCircuit.IsStrict` — a circuit of the literal model [AB09, Def 6.1].
* `BoolCircuit.DAGCircuit.deconst` — remove constants and identity gates (`n ≥ 1`).

## Main results

* `BoolCircuit.DAGCircuit.not_isStrict_zero` — no strict circuit has `0` inputs, which is
  why the library's model admits constants.
* `BoolCircuit.DAGCircuit.IsStrict.fanout_eq_zero_iff` — a strict circuit has exactly one
  sink, its output; `IsStrict.args_ne_nil` — its sources are exactly its inputs.
* `BoolCircuit.DAGCircuit.deconst_eval`, `deconst_strict`, `deconst_size` — for `n ≥ 1`,
  a fan-in-two circuit of size `S` becomes one of size `S + 3` with only strict gates.

## Divergences from [AB09, Def 6.1]

* **Length `0`.**  `IsStrict` is impossible at `n = 0` (`not_isStrict_zero`: the first gate
  has nothing to read).  Taken literally, the book's model has no circuit at all for
  length `0`.

* **No parallel edges (interpretation).**  `DAGGate.Strict` requires the inputs of a gate
  to be distinct: Def 6.1's "directed acyclic graph" is read as a simple graph, as in
  `DAGGate.WellFormed`.  This is conservative: the circuits built here are literal under
  the multigraph reading too.  A gate `∧(v, v)` or `∨(v, v)` costs one extra gate as `¬¬v`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Definition 6.1.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Strict gates and strict circuits -/

/-- A gate of the literal model of [AB09, Def 6.1]: it reads pairwise distinct vertices,
exactly one if it is a `¬` gate and exactly two if it is an `∧` or `∨` gate. -/
def DAGGate.Strict (g : DAGGate) : Prop :=
  g.args.Nodup ∧ g.args.length = if g.kind = .not then 1 else 2

/-- A strict gate is admissible in a fan-in-two circuit. -/
theorem DAGGate.Strict.faninTwo {g : DAGGate} (h : g.Strict) : g.FaninTwo := by
  refine ⟨⟨h.1, fun hk => by simpa [hk] using h.2⟩, ?_⟩
  rw [h.2]; split_ifs <;> omega

/-- A strict gate reads at least one vertex. -/
theorem DAGGate.Strict.args_ne_nil {g : DAGGate} (h : g.Strict) : g.args ≠ [] := by
  intro he
  have := h.2
  rw [he] at this
  split_ifs at this <;> simp at this

/-- A circuit of the literal model of [AB09, Def 6.1]: every `∧`/`∨` gate has fan-in
exactly two and every `¬` gate fan-in exactly one (no constants, no identity gates, no
parallel edges), and every vertex other than the output has fan-out at least one.  The
second condition makes the output the unique sink (`IsStrict.fanout_eq_zero_iff`); the
first makes the inputs the only sources.  [AB09, Def 6.1] -/
def DAGCircuit.IsStrict (C : DAGCircuit n) : Prop :=
  (∀ g ∈ C.gates, g.Strict) ∧ ∀ v < C.size, v ≠ C.output → 0 < C.fanout v

/-- A strict circuit has fan-in two. -/
theorem DAGCircuit.IsStrict.isFaninTwo {C : DAGCircuit n} (h : C.IsStrict) : C.IsFaninTwo :=
  ⟨fun g hg => (h.1 g hg).faninTwo.1, fun g hg => (h.1 g hg).faninTwo.2⟩

/-- Every gate of a strict circuit has an incoming edge, so the sources of a strict
circuit are exactly its `n` inputs.  [AB09, Def 6.1] -/
theorem DAGCircuit.IsStrict.args_ne_nil {C : DAGCircuit n} (h : C.IsStrict) :
    ∀ g ∈ C.gates, g.args ≠ [] :=
  fun g hg => (h.1 g hg).args_ne_nil

/-- No gate reads the last vertex `n + |gs| - 1` of an acyclic gate list. -/
theorem fanoutIn_last_eq_zero {gs : List DAGGate} (hgs : GatesAcyclic n gs) {v : ℕ}
    (hv : n + gs.length ≤ v + 1) : fanoutIn gs v = 0 := by
  rw [fanoutIn, List.countP_eq_zero]
  intro g hg hmem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have := hgs i hi v (of_decide_eq_true hmem)
  omega

/-- The output of a strict circuit is its last vertex. -/
theorem DAGCircuit.IsStrict.output_eq {C : DAGCircuit n} (h : C.IsStrict) :
    C.output = C.size - 1 := by
  have hlt := C.output_lt
  by_contra hne
  have hpos : 0 < C.fanout (C.size - 1) :=
    h.2 _ (by simp only [DAGCircuit.size]; omega) (Ne.symm hne)
  rw [DAGCircuit.fanout, fanoutIn_last_eq_zero C.args_lt
    (by simp only [DAGCircuit.size]; omega)] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **A strict circuit has exactly one sink, its output**: a vertex has fan-out `0` iff it
is the output.  [AB09, Def 6.1] -/
theorem DAGCircuit.IsStrict.fanout_eq_zero_iff {C : DAGCircuit n} (h : C.IsStrict) {v : ℕ}
    (hv : v < C.size) : C.fanout v = 0 ↔ v = C.output := by
  constructor
  · intro h0
    by_contra hne
    have := h.2 v hv hne
    omega
  · rintro rfl
    rw [DAGCircuit.fanout]
    exact fanoutIn_last_eq_zero C.args_lt (by
      have := h.output_eq; have := C.output_lt; simp only [DAGCircuit.size] at *; omega)

/-- **There is no strict circuit with `0` inputs**: its first gate would have no earlier
vertex to read.  This is why the library's model (`DAGCircuit.IsFaninTwo`) admits
constants, i.e. fan-in-zero `∧`/`∨` gates. -/
theorem DAGCircuit.not_isStrict_zero (C : DAGCircuit 0) : ¬ C.IsStrict := by
  intro h
  have hlen : 0 < C.gates.length := by have := C.output_lt; omega
  apply (h.1 _ (List.getElem_mem hlen)).args_ne_nil
  rw [List.eq_nil_iff_forall_not_mem]
  intro a ha
  have := C.args_lt 0 hlen a ha
  omega

/-! ## Removing constants and identity gates -/

/-- The vertex renaming of `deconst`: inputs stay, gate vertices move up by the three
prefix gates. -/
def shiftPrefix (n v : ℕ) : ℕ := if v < n then v else v + 3

/-- Renaming by `shiftPrefix` is injective. -/
theorem shiftPrefix_injective (n : ℕ) : Function.Injective (shiftPrefix n) := by
  intro a b h
  unfold shiftPrefix at h
  split_ifs at h <;> omega

/-- A renamed vertex is never one of the three prefix vertices `n, n + 1, n + 2`. -/
theorem shiftPrefix_ne {v k : ℕ} (hk : k < 3) : shiftPrefix n v ≠ n + k := by
  unfold shiftPrefix; split_ifs <;> omega

/-- A renamed vertex is not the prefix constant `1`. -/
theorem shiftPrefix_ne_one {v : ℕ} : shiftPrefix n v ≠ n + 1 := shiftPrefix_ne (by omega)

/-- A renamed vertex is not the prefix constant `0`. -/
theorem shiftPrefix_ne_two {v : ℕ} : shiftPrefix n v ≠ n + 2 := shiftPrefix_ne (by omega)

/-- A vertex below `n + i` is renamed below `n + 3 + i`. -/
theorem shiftPrefix_lt {v i : ℕ} (hv : v < n + i) : shiftPrefix n v < n + 3 + i := by
  unfold shiftPrefix; split_ifs <;> omega

/-- The three prefix gates of `deconst`: `¬x₀` (vertex `n`), `x₀ ∨ ¬x₀ = 1` (vertex
`n + 1`) and `x₀ ∧ ¬x₀ = 0` (vertex `n + 2`). -/
def constPrefix (n : ℕ) : List DAGGate := [⟨.not, [0]⟩, ⟨.or, [0, n]⟩, ⟨.and, [0, n]⟩]

/-- The strict replacement of a fan-in-two gate, reading the renamed vertices
(`shiftPrefix`) and the prefix constants `1 = n + 1`, `0 = n + 2`: the constant `1`
becomes `1 ∨ 0`, the constant `0` becomes `1 ∧ 0`, the identity `∧(a)` becomes `a ∧ 1`, the
identity `∨(a)` becomes `a ∨ 0`, and every other gate is renamed. -/
def strictGate (n : ℕ) : DAGGate → DAGGate
  | ⟨.and, []⟩ => ⟨.or, [n + 1, n + 2]⟩
  | ⟨.or, []⟩ => ⟨.and, [n + 1, n + 2]⟩
  | ⟨.and, [a]⟩ => ⟨.and, [shiftPrefix n a, n + 1]⟩
  | ⟨.or, [a]⟩ => ⟨.or, [shiftPrefix n a, n + 2]⟩
  | ⟨k, args⟩ => ⟨k, args.map (shiftPrefix n)⟩

/-- `strictGate` reads renamed inputs of the old gate, or the prefix constants. -/
theorem strictGate_args (g : DAGGate) :
    ∀ b ∈ (strictGate n g).args, (∃ a ∈ g.args, b = shiftPrefix n a) ∨ b = n + 1 ∨
      b = n + 2 := by
  rcases g with ⟨k, _ | ⟨a, _ | ⟨c, l⟩⟩⟩ <;> cases k <;> intro b hb <;>
    simp only [strictGate, List.mem_cons, List.mem_map, List.not_mem_nil] at hb ⊢ <;>
    aesop

/-- `strictGate` turns a fan-in-two gate into a strict gate. -/
theorem strictGate_strict {g : DAGGate} (hg : g.FaninTwo) : (strictGate n g).Strict := by
  obtain ⟨⟨hnd, hnot⟩, hle⟩ := hg
  have hinj := shiftPrefix_injective n
  rcases g with ⟨k, _ | ⟨a, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> cases k <;>
    simp at hnot hle hnd <;>
    simp [strictGate, DAGGate.Strict, hinj.eq_iff, hnd, shiftPrefix_ne_one, shiftPrefix_ne_two]

/-- `strictGate` computes the old gate, when every renamed input carries the old input's
value and the prefix vertices `n + 1`, `n + 2` carry `1` and `0`. -/
theorem strictGate_eval {g : DAGGate} (hg : g.FaninTwo) {vals vals' : List Bool}
    (hT : vals.getD (n + 1) false = true) (hF : vals.getD (n + 2) false = false)
    (h : ∀ a ∈ g.args, vals.getD (shiftPrefix n a) false = vals'.getD a false) :
    (strictGate n g).eval vals = g.eval vals' := by
  obtain ⟨⟨hnd, hnot⟩, hle⟩ := hg
  simp only [List.getD_eq_getElem?_getD] at hT hF h
  rcases g with ⟨k, _ | ⟨a, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> cases k <;>
    simp at hnot hle h <;>
    simp [strictGate, DAGGate.eval, hT, hF, h]

/-- The gates of `deconst` read only earlier vertices. -/
theorem deconst_acyclic (gs : List DAGGate) (hgs : GatesAcyclic n gs) (hn : 0 < n) :
    GatesAcyclic n (constPrefix n ++ gs.map (strictGate n)) := by
  refine gatesAcyclic_append.mpr ⟨?_, ?_⟩
  · simp only [constPrefix, gatesAcyclic_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, gatesAcyclic_nil, and_true]
    omega
  · intro i hi b hb
    simp only [List.getElem_map] at hb
    simp only [List.length_map] at hi
    have hlen : (constPrefix n).length = 3 := rfl
    rw [hlen]
    rcases strictGate_args _ b hb with ⟨a, ha, rfl⟩ | rfl | rfl
    · exact shiftPrefix_lt (hgs i hi a ha)
    · omega
    · omega

/-- **Removing constants and identity gates.**  For `n ≥ 1`, the circuit that first
computes `¬x₀`, `1 = x₀ ∨ ¬x₀` and `0 = x₀ ∧ ¬x₀`, then replaces every gate by its
`strictGate` (constants become `1 ∨ 0` and `1 ∧ 0`, identities `a ∧ 1` and `a ∨ 0`). -/
def DAGCircuit.deconst (C : DAGCircuit n) (hn : 0 < n) : DAGCircuit n where
  gates := constPrefix n ++ C.gates.map (strictGate n)
  output := shiftPrefix n C.output
  args_lt := deconst_acyclic C.gates C.args_lt hn
  output_lt := by
    have := shiftPrefix_lt (n := n) (i := C.gates.length) C.output_lt
    simp only [List.length_append, List.length_map]
    exact lt_of_lt_of_le this (by simp [constPrefix]; omega)

section Deconst

variable (C : DAGCircuit n) (hn : 0 < n)

/-- `deconst` adds exactly the three prefix gates. -/
@[simp] theorem DAGCircuit.deconst_size : (C.deconst hn).size = C.size + 3 := by
  simp [DAGCircuit.deconst, DAGCircuit.size, constPrefix]; omega

/-- Every gate of `deconst` of a fan-in-two circuit is strict. -/
theorem DAGCircuit.deconst_strict (hC : C.IsFaninTwo) : ∀ g ∈ (C.deconst hn).gates, g.Strict := by
  intro g hg
  simp only [DAGCircuit.deconst, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g, hg, rfl⟩
  · simp only [constPrefix, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp [DAGGate.Strict] <;> omega
  · exact strictGate_strict ⟨hC.1 g hg, hC.2 g hg⟩

/-- `deconst` computes every old vertex at its renamed vertex.

**Proof sketch.** The prefix computes `¬x₀`, then `x₀ ∨ ¬x₀ = 1` and `x₀ ∧ ¬x₀ = 0`.  By
strong induction on the old vertex `v`: an input is unchanged; old gate `i` sits at new
gate `i + 3`, which is its `strictGate`, and every input of the old gate is an earlier
vertex, carried by the induction hypothesis to its renamed vertex; `strictGate_eval`
concludes. -/
theorem DAGCircuit.deconst_values (hC : C.IsFaninTwo) (x : Fin n → Bool) :
    ∀ v < n + C.gates.length,
      ((C.deconst hn).values x).getD (shiftPrefix n v) false = (C.values x).getD v false := by
  set V := (C.deconst hn).values x with hV
  have hlen : (C.deconst hn).gates.length = C.gates.length + 3 := by
    simp [DAGCircuit.deconst, constPrefix]
  -- the prefix constants
  have hg0 : (C.deconst hn).gates[0]'(by omega) = ⟨.not, [0]⟩ := rfl
  have hg1 : (C.deconst hn).gates[1]'(by omega) = ⟨.or, [0, n]⟩ := rfl
  have hg2 : (C.deconst hn).gates[2]'(by omega) = ⟨.and, [0, n]⟩ := rfl
  have h0 : V.getD (n + 0) false = !V.getD 0 false := by
    rw [hV, (C.deconst hn).values_getD_gate x (i := 0) (by omega), hg0]
    simp [DAGGate.eval]
  have hT : V.getD (n + 1) false = true := by
    rw [hV, (C.deconst hn).values_getD_gate x (i := 1) (by omega), hg1,
      DAGGate.eval_pair (by decide), ← hV, show n = n + 0 from rfl, h0]
    cases V.getD 0 false <;> rfl
  have hF : V.getD (n + 2) false = false := by
    rw [hV, (C.deconst hn).values_getD_gate x (i := 2) (by omega), hg2,
      DAGGate.eval_pair (by decide), ← hV, show n = n + 0 from rfl, h0]
    cases V.getD 0 false <;> rfl
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hvn : v < n
    · have h1 := (C.deconst hn).values_getD_input x ⟨v, hvn⟩
      have h2 := C.values_getD_input x ⟨v, hvn⟩
      simp only at h1 h2
      rw [show shiftPrefix n v = v by simp [shiftPrefix, hvn], h1, h2]
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hvn)
      have hi : i < C.gates.length := by omega
      have hs : shiftPrefix n (n + i) = n + (i + 3) := by simp [shiftPrefix]; omega
      rw [hs, (C.deconst hn).values_getD_gate x (by omega), C.values_getD_gate x hi]
      have hget : (C.deconst hn).gates[i + 3]'(by omega) = strictGate n C.gates[i] := by
        simp [DAGCircuit.deconst, constPrefix]
      rw [hget]
      exact strictGate_eval ⟨hC.1 _ (List.getElem_mem hi), hC.2 _ (List.getElem_mem hi)⟩
        hT hF fun a ha => ih a (by have := C.args_lt i hi a ha; omega)
          (by have := C.args_lt i hi a ha; omega)

/-- `deconst` computes the same function. -/
theorem DAGCircuit.deconst_eval (hC : C.IsFaninTwo) (x : Fin n → Bool) :
    (C.deconst hn).eval x = C.eval x :=
  C.deconst_values hn hC x _ C.output_lt

end Deconst

end BoolCircuit
