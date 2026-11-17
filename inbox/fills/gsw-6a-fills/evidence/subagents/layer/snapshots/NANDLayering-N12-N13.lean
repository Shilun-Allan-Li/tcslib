/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Fin.Tuple.Basic
import TCSlib.Complexity.CircuitComplexity.NANDForm

/-!
# Layering NAND-form `DAGCircuit`s

A circuit is *layered* (`BoolCircuit.DAGCircuit.IsLayered`) when every gate sits exactly one level
above each vertex it reads: `C.depthAt a + 1 = C.depthAt (n + i)` for every argument `a` of gate
`i`.  Inputs are at level `0` and fan-in-0 gates at level `1`, so a layered circuit evaluates
level by level.

The conversion `BoolCircuit.DAGCircuit.layerNAND` takes a NAND-form circuit `C` on `n ≥ 1` inputs
to a layered NAND-form circuit on the `2n` **literals** `x, ¬x` (`BoolCircuit.litInput`), of the
same depth and function.

**Why literals (the odd-gap finding).** Call a vertex's depth its level.  In a layered NAND
circuit whose only level-0 vertices are the positive inputs, induction on the level shows that
every vertex at an even level computes a monotone function and every vertex at an odd level an
antimonotone one (constants are both; the NAND of antimonotone functions is monotone, and
conversely).  XOR is neither, so over positive inputs no layering exists in general: an odd gap
cannot always be padded.  With both literals at level `0` every vertex is available at both
parities.  Literal inputs are Bar89's "inputs and negated inputs" [Bar89, Thm 1, p003-b002].

**Construction** (computable, by columns in topological order; no NAND-form hypothesis).  Write
`D := C.depth` and `δ := C.depthAt v`.  Each old vertex `v` with `δ ≤ D` gets a *column* of new
vertices `v@k`, one for every level `δ ≤ k ≤ D`, with `v@k` at depth exactly `k`:
* **base** `v@δ`: an input `xᵢ` is input vertex `i`; a gate is a NAND gate over its arguments'
  copies `a@(δ - 1)`;
* **parity twin** `v@(δ + 1)`: an input's twin is `NAND(¬xᵢ)`, reading input vertex `n + i`; a
  gate's twin is the same NAND gate over `a@δ`; a fan-in-0 gate's twin is `NAND(NAND(x₀, ¬x₀))`,
  which needs `n ≥ 1`;
* **double-NAND chain** `v@k = NAND(NAND(v@(k - 2)))` for `k ≥ δ + 2`, the inner gate at level
  `k - 1`.

Every gate is emitted as a NAND gate `⟨.not, args⟩`.  Old vertices deeper than `D` are dead and
get no column.  The output is `out@D`.  The gate list (`layerGates`) and output vertex
(`layerOutput`) are definitions; the structure fields of `DAGCircuit` (acyclicity, output in
range) are the targets N12–N13, as N2 is for `toNANDForm`, so while they are admitted `sorryAx`
reaches `layerNAND` through them only.

**Column invariant** (the plan of every target's fill): after the fold has processed the old
vertices `0, …, v - 1`, for every processed `u` with `C.depthAt u ≤ D` and every level
`C.depthAt u ≤ k ≤ D`, the recorded vertex `u@k` exists below the current vertex count, has depth
exactly `k`, reads only vertices of depth `k - 1`, and, when `C.IsNANDForm`, has on
`litInput x` the value of `u` on `x`; the column of `u` has at most `2 (D - C.depthAt u) + 1`
gates.  It is proved by induction along the fold.

**Not reused.** `DAGCircuit.toLayered` and `TreeCircuit.toLayered` (`LayeredDAG.lean`) map into
the other model `LayeredCircuit` with one vertex per layer (depth = number of gates) and need
`IsWellFormed` and no `∨`; the conversion here keeps the `DAGCircuit` model and its depth, and is
named `layerNAND`, not `toLayered`.  It is not an instance of `DAGCircuit.rewrite`: the input
count changes and the depth must be exact, not bounded.  The column fold is a construction, not
a host: its contract does not vary by consumer.

No ingested passage defines layered circuits or a layering conversion: the conversion is glue,
motivated by the level-by-level evaluation of [BV11, Thm 3.1, p015-b001; Def 3.6, p014-b001]
("depth-`L` binary arithmetic circuits", an evaluation key whose length depends on `L`).

## Main definitions

* `BoolCircuit.DAGCircuit.IsLayered` — every gate is one level above each vertex it reads.
* `BoolCircuit.litInput` — the `2n` literals of an input.
* `BoolCircuit.layerChain`, `BoolCircuit.DAGCircuit.layerAt`, `BoolCircuit.DAGCircuit.layerColumn`,
  `BoolCircuit.DAGCircuit.layerFold` — the column builder.
* `BoolCircuit.DAGCircuit.layerGates`, `BoolCircuit.DAGCircuit.layerOutput` — the gates and the
  output vertex of the layering.
* `BoolCircuit.DAGCircuit.layerNAND` — the layering conversion.

## Main results

All are statement-phase targets (glue):
* `BoolCircuit.DAGCircuit.layerGates_acyclic`, `layerOutput_lt` (N12–N13) — the structure fields.
* `BoolCircuit.DAGCircuit.layerNAND_eval` (N7) — semantics on the literal input.
* `BoolCircuit.DAGCircuit.layerNAND_isLayered` (N8), `layerNAND_isNANDForm` (N9).
* `BoolCircuit.DAGCircuit.layerNAND_depth` (N10) — depth preserved exactly.
* `BoolCircuit.DAGCircuit.layerNAND_size_le` (N11) — size `≤ 2n + (2 · depth + 1) · size`.

## References

* [Bar89] D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly
  those languages in NC¹*, J. Comput. Syst. Sci. 38(1):150–164, 1989.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient fully homomorphic encryption from (standard)
  LWE*, FOCS 2011 (full version).
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Layered circuits and literal inputs -/

/-- `C` is *layered*: every gate sits exactly one level above each vertex it reads,
`C.depthAt a + 1 = C.depthAt (n + i)` for every argument `a` of every gate `i` (inputs at level
`0`).  Glue, motivated by the level-by-level evaluation of [BV11, Thm 3.1, p015-b001;
Def 3.6, p014-b001]. -/
def DAGCircuit.IsLayered (C : DAGCircuit n) : Prop :=
  ∀ (i : ℕ) (hi : i < C.gates.length), ∀ a ∈ (C.gates[i]).args,
    C.depthAt a + 1 = C.depthAt (n + i)

/-- Layeredness unfolded: `C.IsLayered ↔ ∀ i (hi : i < C.gates.length), ∀ a ∈ (C.gates[i]).args,
C.depthAt a + 1 = C.depthAt (n + i)`. -/
theorem DAGCircuit.isLayered_iff (C : DAGCircuit n) :
    C.IsLayered ↔ ∀ (i : ℕ) (hi : i < C.gates.length), ∀ a ∈ (C.gates[i]).args,
      C.depthAt a + 1 = C.depthAt (n + i) :=
  Iff.rfl

instance DAGCircuit.decidableIsLayered (C : DAGCircuit n) : Decidable C.IsLayered :=
  @Nat.decidableBallLT C.gates.length
    (fun i hi => ∀ a ∈ (C.gates[i]).args, C.depthAt a + 1 = C.depthAt (n + i))
    (fun i hi => List.decidableBAll _ _)

/-- The *literal input* of `x`: the `2n` literals, positive ones first,
`litInput x = Fin.append x (fun i => !x i)` (Bar89's "inputs and negated inputs"
[Bar89, Thm 1, p003-b002]). -/
def litInput (x : Fin n → Bool) : Fin (n + n) → Bool := Fin.append x fun i => !x i

/-- The literal input unfolded: `litInput x = Fin.append x (fun i => !x i)`. -/
theorem litInput_eq (x : Fin n → Bool) : litInput x = Fin.append x fun i => !x i := rfl

/-- The positive half of the literal input: `litInput x (Fin.castAdd n i) = x i`. -/
theorem litInput_castAdd (x : Fin n → Bool) (i : Fin n) : litInput x (Fin.castAdd n i) = x i := by
  rw [litInput_eq, Fin.append_left]

/-- The negative half of the literal input: `litInput x (Fin.natAdd n i) = !x i`. -/
theorem litInput_natAdd (x : Fin n → Bool) (i : Fin n) : litInput x (Fin.natAdd n i) = !x i := by
  rw [litInput_eq, Fin.append_right]

/-! ## The column builder -/

/-- The **double-NAND chain**: after the gates `gs` of a circuit with `N` inputs, with `a` and
`b` the copies of a vertex at the two levels below the next one, append `s` links; link `t`
appends the inner gate `NAND(a)` (vertex `N + |gs|`) and the outer gate `NAND(NAND(a))` (vertex
`N + |gs| + 1`), which becomes the copy two levels above `a`.  Returns the new gate list and the
outer vertices, in level order:
`layerChain N gs a b 0 = (gs, [])` and `layerChain N gs a b (s + 1) =
let r := layerChain N (gs ++ [⟨.not, [a]⟩, ⟨.not, [N + |gs|]⟩]) b (N + |gs| + 1) s;
(r.1, (N + |gs| + 1) :: r.2)`.  Glue (plan section r3 §H3.13). -/
def layerChain (N : ℕ) : List DAGGate → ℕ → ℕ → ℕ → List DAGGate × List ℕ
  | gs, _, _, 0 => (gs, [])
  | gs, a, b, s + 1 =>
    let r := layerChain N (gs ++ [⟨.not, [a]⟩, ⟨.not, [N + gs.length]⟩]) b (N + gs.length + 1) s
    (r.1, (N + gs.length + 1) :: r.2)

/-- The empty chain: `layerChain N gs a b 0 = (gs, [])`. -/
theorem layerChain_zero (N : ℕ) (gs : List DAGGate) (a b : ℕ) :
    layerChain N gs a b 0 = (gs, []) := rfl

/-- One more link: `layerChain N gs a b (s + 1) = ((layerChain N gs' b (N + |gs| + 1) s).1,
(N + |gs| + 1) :: (layerChain N gs' b (N + |gs| + 1) s).2)` with
`gs' = gs ++ [⟨.not, [a]⟩, ⟨.not, [N + |gs|]⟩]`. -/
theorem layerChain_succ (N : ℕ) (gs : List DAGGate) (a b s : ℕ) :
    layerChain N gs a b (s + 1) =
      ((layerChain N (gs ++ [⟨.not, [a]⟩, ⟨.not, [N + gs.length]⟩]) b (N + gs.length + 1) s).1,
        (N + gs.length + 1) ::
          (layerChain N (gs ++ [⟨.not, [a]⟩, ⟨.not, [N + gs.length]⟩]) b
            (N + gs.length + 1) s).2) := rfl

/-- The copy `v@k` recorded in the columns `cols` (column `v` lists `v@δ, v@(δ + 1), …` with
`δ = C.depthAt v`): `C.layerAt cols v k = (cols.getD v []).getD (k - C.depthAt v) 0`.  Glue. -/
def DAGCircuit.layerAt (C : DAGCircuit n) (cols : List (List ℕ)) (v k : ℕ) : ℕ :=
  (cols.getD v []).getD (k - C.depthAt v) 0

/-- The recorded copy unfolded: `C.layerAt cols v k = (cols.getD v []).getD (k - C.depthAt v) 0`. -/
theorem DAGCircuit.layerAt_eq (C : DAGCircuit n) (cols : List (List ℕ)) (v k : ℕ) :
    C.layerAt cols v k = (cols.getD v []).getD (k - C.depthAt v) 0 := rfl

/-- One step of the column fold: build the column of the old vertex `v` after the state
`s = (new gates, columns of 0, …, v - 1)`, over the `n + n` literal inputs.  With `D = C.depth`,
`δ = C.depthAt v` and `m = n + n + |s.1|` (the next new vertex):
* `D < δ` (dead vertex): no gate, empty column;
* `v < n` (input), `D = 0`: column `[v]`;
* `v < n`, `D ≥ 1`: twin `NAND[n + v]` (vertex `m`), then `D - 1` chain links from `(v, m)`;
  column `v :: m :: chain`;
* gate `g = C.gates.getD (v - n) ⟨.not, []⟩`: base `NAND[a@(δ - 1) | a ∈ g.args]` (vertex `m`);
  if `D = δ` the column is `[m]`; otherwise the twin is `NAND[a@δ | a ∈ g.args]` (vertex
  `m + 1`), or, when `g.args = []`, `NAND[0, n]` then `NAND[m + 1]` (twin vertex `m + 2`); then
  `D - δ - 1` chain links from `(m, twin)`; column `m :: twin :: chain`.
Glue (plan section r3 §H3.13). -/
def DAGCircuit.layerColumn (C : DAGCircuit n) (s : List DAGGate × List (List ℕ)) (v : ℕ) :
    List DAGGate × List (List ℕ) :=
  if C.depth < C.depthAt v then (s.1, s.2 ++ [[]])
  else if v < n then
    if C.depth = 0 then (s.1, s.2 ++ [[v]])
    else
      let r := layerChain (n + n) (s.1 ++ [⟨.not, [n + v]⟩]) v (n + n + s.1.length) (C.depth - 1)
      (r.1, s.2 ++ [v :: (n + n + s.1.length) :: r.2])
  else
    let g := C.gates.getD (v - n) ⟨.not, []⟩
    let m := n + n + s.1.length
    let gs₁ := s.1 ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v - 1)⟩]
    if C.depth = C.depthAt v then (gs₁, s.2 ++ [[m]])
    else
      let tw : List DAGGate × ℕ :=
        if g.args = [] then (gs₁ ++ [⟨.not, [0, n]⟩, ⟨.not, [m + 1]⟩], m + 2)
        else (gs₁ ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v)⟩], m + 1)
      let r := layerChain (n + n) tw.1 m tw.2 (C.depth - C.depthAt v - 1)
      (r.1, s.2 ++ [m :: tw.2 :: r.2])

/-- The fold step unfolded (`C.layerColumn s v` is the case split of its docstring).

**Proof sketch.** Definitional: `rfl`. -/
theorem DAGCircuit.layerColumn_eq (C : DAGCircuit n) (s : List DAGGate × List (List ℕ)) (v : ℕ) :
    C.layerColumn s v =
      if C.depth < C.depthAt v then (s.1, s.2 ++ [[]])
      else if v < n then
        if C.depth = 0 then (s.1, s.2 ++ [[v]])
        else
          ((layerChain (n + n) (s.1 ++ [⟨.not, [n + v]⟩]) v (n + n + s.1.length)
              (C.depth - 1)).1,
            s.2 ++ [v :: (n + n + s.1.length) ::
              (layerChain (n + n) (s.1 ++ [⟨.not, [n + v]⟩]) v (n + n + s.1.length)
                (C.depth - 1)).2])
      else
        if C.depth = C.depthAt v then
          (s.1 ++ [⟨.not, (C.gates.getD (v - n) ⟨.not, []⟩).args.map fun a =>
              C.layerAt s.2 a (C.depthAt v - 1)⟩], s.2 ++ [[n + n + s.1.length]])
        else
          let gs₁ := s.1 ++ [⟨.not, (C.gates.getD (v - n) ⟨.not, []⟩).args.map fun a =>
              C.layerAt s.2 a (C.depthAt v - 1)⟩]
          let tw : List DAGGate × ℕ :=
            if (C.gates.getD (v - n) ⟨.not, []⟩).args = [] then
              (gs₁ ++ [⟨.not, [0, n]⟩, ⟨.not, [n + n + s.1.length + 1]⟩],
                n + n + s.1.length + 2)
            else
              (gs₁ ++ [⟨.not, (C.gates.getD (v - n) ⟨.not, []⟩).args.map fun a =>
                C.layerAt s.2 a (C.depthAt v)⟩], n + n + s.1.length + 1)
          ((layerChain (n + n) tw.1 (n + n + s.1.length) tw.2
              (C.depth - C.depthAt v - 1)).1,
            s.2 ++ [(n + n + s.1.length) :: tw.2 ::
              (layerChain (n + n) tw.1 (n + n + s.1.length) tw.2
                (C.depth - C.depthAt v - 1)).2]) := rfl

/-- The column fold over the old vertices `0, …, n + |C.gates| - 1` in topological order:
`C.layerFold = (List.range (n + C.gates.length)).foldl C.layerColumn ([], [])`.  Glue. -/
def DAGCircuit.layerFold (C : DAGCircuit n) : List DAGGate × List (List ℕ) :=
  (List.range (n + C.gates.length)).foldl C.layerColumn ([], [])

/-- The column fold unfolded:
`C.layerFold = (List.range (n + C.gates.length)).foldl C.layerColumn ([], [])`. -/
theorem DAGCircuit.layerFold_eq (C : DAGCircuit n) :
    C.layerFold = (List.range (n + C.gates.length)).foldl C.layerColumn ([], []) := rfl

/-- The gate list of the layering (plan section r3 §H3.13): `C.layerGates = C.layerFold.1`, every
old vertex `v` realized at each level `C.depthAt v ≤ k ≤ C.depth` (base, parity twin, double-NAND
chain), every gate emitted as a NAND gate, columns in topological order.  Computable; glue
(no ingested source, r3 §H1 gap 4). -/
def DAGCircuit.layerGates [NeZero n] (C : DAGCircuit n) : List DAGGate := C.layerFold.1

/-- The layering's gates unfolded: `C.layerGates = C.layerFold.1`. -/
theorem DAGCircuit.layerGates_eq [NeZero n] (C : DAGCircuit n) :
    C.layerGates = C.layerFold.1 := rfl

/-- The output vertex of the layering, `out@(C.depth)`:
`C.layerOutput = C.layerAt C.layerFold.2 C.output C.depth`.  Computable; glue. -/
def DAGCircuit.layerOutput [NeZero n] (C : DAGCircuit n) : ℕ :=
  C.layerAt C.layerFold.2 C.output C.depth

/-- The layering's output unfolded: `C.layerOutput = C.layerAt C.layerFold.2 C.output C.depth`. -/
theorem DAGCircuit.layerOutput_eq [NeZero n] (C : DAGCircuit n) :
    C.layerOutput = C.layerAt C.layerFold.2 C.output C.depth := rfl

/-- The chain only extends the gate list: `gs <+: (layerChain N gs a b s).1`.  Glue. -/
private theorem layerChain_isPrefix {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, gs <+: (layerChain N gs a b s).1
  | 0, gs, a, b => by rw [layerChain_zero]
  | s + 1, gs, a, b => by
    rw [layerChain_succ]
    exact (List.prefix_append _ _).trans layerChain_isPrefix

/-- The chain appends two gates per link:
`(layerChain N gs a b s).1.length = gs.length + 2 * s`.  Glue. -/
private theorem length_layerChain_fst {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, (layerChain N gs a b s).1.length = gs.length + 2 * s
  | 0, gs, a, b => by rw [layerChain_zero]; rfl
  | s + 1, gs, a, b => by
    rw [layerChain_succ, length_layerChain_fst, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega

/-- Every gate the chain appends reads one vertex: `g ∈ (layerChain N gs a b s).1 →
g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩`.  Glue. -/
private theorem mem_layerChain_fst {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ} {g : DAGGate}, g ∈ (layerChain N gs a b s).1 →
      g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩
  | 0, gs, a, b, g, hg => by rw [layerChain_zero] at hg; exact Or.inl hg
  | s + 1, gs, a, b, g, hg => by
    rw [layerChain_succ] at hg
    rcases mem_layerChain_fst hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact Or.inl hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr hg

/-- Every outer vertex the chain records lies below the final vertex count:
`w ∈ (layerChain N gs a b s).2 → w < N + gs.length + 2 * s`.  Glue. -/
private theorem layerChain_snd_lt {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b w : ℕ}, w ∈ (layerChain N gs a b s).2 →
      w < N + gs.length + 2 * s
  | 0, gs, a, b, w, hw => by rw [layerChain_zero] at hw; exact absurd hw List.not_mem_nil
  | s + 1, gs, a, b, w, hw => by
    rw [layerChain_succ] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · omega
    · have := layerChain_snd_lt hw
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega

/-- The chain keeps a gate list acyclic when its two start vertices exist:
`GatesAcyclic N gs → a < N + gs.length → b < N + gs.length →
GatesAcyclic N (layerChain N gs a b s).1`.  Glue. -/
private theorem layerChain_acyclic {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, GatesAcyclic N gs → a < N + gs.length →
      b < N + gs.length → GatesAcyclic N (layerChain N gs a b s).1
  | 0, gs, a, b, h, _, _ => by rw [layerChain_zero]; exact h
  | s + 1, gs, a, b, h, ha, hb => by
    rw [layerChain_succ]
    have h1 := h.snoc (g := ⟨.not, [a]⟩) (by simpa using ha)
    have h2 := h1.snoc (g := ⟨.not, [N + gs.length]⟩) (by simp)
    rw [List.append_assoc] at h2
    exact layerChain_acyclic h2 (by simp; omega) (by simp; omega)

/-- A recorded copy is below any positive bound `B` of all column entries:
`0 < B → (∀ col ∈ cols, ∀ w ∈ col, w < B) → C.layerAt cols v k < B` (a missing copy reads as
`0`).  Glue. -/
private theorem DAGCircuit.layerAt_lt (C : DAGCircuit n) {cols : List (List ℕ)} {B : ℕ}
    (hB : 0 < B) (h : ∀ col ∈ cols, ∀ w ∈ col, w < B) (v k : ℕ) : C.layerAt cols v k < B := by
  rw [layerAt_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases hc : cols[v]? with _ | col
  · simpa using hB
  · rcases hw : col[k - C.depthAt v]? with _ | w
    · simpa [hw] using hB
    · simpa [hw] using h col (List.mem_of_getElem? hc) w (List.mem_of_getElem? hw)

/-- One fold step, structurally: if the gates `s.1` are acyclic over the `n + n` literal inputs
and every column entry of `s.2` lies below `n + n + |s.1|`, then `C.layerColumn s v` appends one
column `col` with entries below its new vertex count, extends `s.1` (`s.1 <+: _`) acyclically by
at most `2 * C.depth + 1` gates, and keeps every gate a NAND gate when `C.IsNANDForm`.  Glue.

**Proof sketch.** Case split along `layerColumn_eq`.  Dead vertex and input with `D = 0`: no
gate.  Input: the twin `NAND[n + v]` reads an input, then `D - 1` chain links
(`layerChain_acyclic`, `length_layerChain_fst`, `layerChain_snd_lt`).  Gate: the base reads
recorded copies (`layerAt_lt`); the twin reads copies, or `NAND[0, n]` then `NAND[m + 1]`; then
`D - δ - 1` links.  The NAND-gate property comes from `isNAND_iff` (the copies keep the old
fan-in, the old gate is a NAND gate or the default `⟨.not, []⟩`) and `mem_layerChain_fst`. -/
private theorem DAGCircuit.layerColumn_struct [NeZero n] (C : DAGCircuit n)
    (s : List DAGGate × List (List ℕ)) (v : ℕ) (hacy : GatesAcyclic (n + n) s.1)
    (hcol : ∀ col ∈ s.2, ∀ w ∈ col, w < n + n + s.1.length)
    (hnand : C.IsNANDForm → ∀ g ∈ s.1, g.IsNAND) :
    (∃ col, (C.layerColumn s v).2 = s.2 ++ [col] ∧
      ∀ w ∈ col, w < n + n + (C.layerColumn s v).1.length) ∧
    s.1 <+: (C.layerColumn s v).1 ∧ GatesAcyclic (n + n) (C.layerColumn s v).1 ∧
    (C.IsNANDForm → ∀ g ∈ (C.layerColumn s v).1, g.IsNAND) ∧
    (C.layerColumn s v).1.length ≤ s.1.length + (2 * C.depth + 1) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have hL : ∀ u k, C.layerAt s.2 u k < n + n + s.1.length := fun u k =>
    C.layerAt_lt (by omega) hcol u k
  have h1 : ∀ w : ℕ, (⟨.not, [w]⟩ : DAGGate).IsNAND := fun w =>
    (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
  -- the NAND property of a gate list followed by a chain
  have hch : ∀ (gs : List DAGGate) (g : DAGGate), (∀ g ∈ gs, g.IsNAND) →
      ∀ {t a b : ℕ}, g ∈ (layerChain (n + n) gs a b t).1 → g.IsNAND := by
    intro gs g hgs t a b hg
    rcases mem_layerChain_fst hg with hg | ⟨w, rfl⟩
    · exact hgs g hg
    · exact h1 w
  rw [layerColumn_eq]
  by_cases hd : C.depth < C.depthAt v
  · rw [if_pos hd]
    exact ⟨⟨[], rfl, by simp⟩, List.prefix_refl _, hacy, hnand, by simp⟩
  rw [if_neg hd]
  by_cases hv : v < n
  · rw [if_pos hv]
    by_cases h3 : C.depth = 0
    · rw [if_pos h3]
      exact ⟨⟨[v], rfl, by simp; omega⟩, List.prefix_refl _, hacy, hnand, by simp⟩
    rw [if_neg h3]
    have hacy0 : GatesAcyclic (n + n) (s.1 ++ [⟨.not, [n + v]⟩]) := hacy.snoc (by simp; omega)
    refine ⟨⟨_, rfl, ?_⟩, (List.prefix_append _ _).trans layerChain_isPrefix,
      layerChain_acyclic hacy0 (by simp; omega) (by simp), fun hC g hg => hch _ g (by
        intro g' hg'
        rcases List.mem_append.mp hg' with hg' | hg'
        · exact hnand hC g' hg'
        · rw [List.mem_singleton.mp hg']; exact h1 _) hg, ?_⟩
    · intro w hw
      rw [length_layerChain_fst]
      simp only [List.mem_cons] at hw
      rcases hw with rfl | rfl | hw
      · simp; omega
      · simp; omega
      · have := layerChain_snd_lt hw
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
    · rw [length_layerChain_fst]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [if_neg hv]
  have hgN : C.IsNANDForm → (C.gates.getD (v - n) ⟨.not, []⟩).IsNAND := by
    intro hC
    rw [List.getD_eq_getElem?_getD]
    rcases hg : C.gates[v - n]? with _ | g
    · exact (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
    · exact (DAGCircuit.isNANDForm_iff C).mp hC g (List.mem_of_getElem? hg)
  generalize C.gates.getD (v - n) ⟨.not, []⟩ = g at hgN ⊢
  have hb0 : ∀ k, GatesAcyclic (n + n)
      (s.1 ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩]) := fun k =>
    hacy.snoc (by simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact hL a k)
  have hbN : ∀ k, C.IsNANDForm →
      (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).IsNAND := fun k hC =>
    (DAGGate.isNAND_iff _).mpr ⟨rfl, by simpa using ((DAGGate.isNAND_iff g).mp (hgN hC)).2⟩
  by_cases h4 : C.depth = C.depthAt v
  · rw [if_pos h4]
    refine ⟨⟨_, rfl, by simp⟩, List.prefix_append _ _, hb0 _, ?_, by simp⟩
    intro hC g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hnand hC g' hg'
    · rw [List.mem_singleton.mp hg']; exact hbN _ hC
  rw [if_neg h4]
  dsimp only
  by_cases h5 : g.args = []
  · rw [if_pos h5]
    dsimp only
    have hacy1 : GatesAcyclic (n + n) (s.1 ++ [⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt v - 1)⟩] ++
          [⟨.not, [0, n]⟩, ⟨.not, [n + n + s.1.length + 1]⟩]) := by
      have h2 := (hb0 (C.depthAt v - 1)).snoc (g := ⟨.not, [0, n]⟩) (by simp; omega)
      have h3 := h2.snoc (g := ⟨.not, [n + n + s.1.length + 1]⟩) (by simp; omega)
      simpa using h3
    have hgs : C.IsNANDForm → ∀ g' ∈ s.1 ++ [⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt v - 1)⟩] ++
          [⟨.not, [0, n]⟩, ⟨.not, [n + n + s.1.length + 1]⟩], g'.IsNAND := by
      intro hC g' hg'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with (hg' | rfl) | rfl | rfl
      · exact hnand hC g' hg'
      · exact hbN _ hC
      · exact (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
      · exact h1 _
    refine ⟨⟨_, rfl, ?_⟩,
      ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans layerChain_isPrefix,
      layerChain_acyclic hacy1 (by simp) (by simp; omega), fun hC g' hg' =>
        hch _ g' (hgs hC) hg', ?_⟩
    · intro w hw
      rw [length_layerChain_fst]
      simp only [List.mem_cons] at hw
      rcases hw with rfl | rfl | hw
      · simp; omega
      · simp; omega
      · have := layerChain_snd_lt hw
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
    · rw [length_layerChain_fst]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · rw [if_neg h5]
    dsimp only
    have hacy1 : GatesAcyclic (n + n) (s.1 ++ [⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt v - 1)⟩] ++
          [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v)⟩]) :=
      (hb0 (C.depthAt v - 1)).snoc (by
        simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; have := hL a (C.depthAt v); simp; omega)
    have hgs : C.IsNANDForm → ∀ g' ∈ s.1 ++ [⟨.not, g.args.map fun a =>
        C.layerAt s.2 a (C.depthAt v - 1)⟩] ++
          [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v)⟩], g'.IsNAND := by
      intro hC g' hg'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
      rcases hg' with (hg' | rfl) | rfl
      · exact hnand hC g' hg'
      · exact hbN _ hC
      · exact hbN _ hC
    refine ⟨⟨_, rfl, ?_⟩,
      ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans layerChain_isPrefix,
      layerChain_acyclic hacy1 (by simp) (by simp; omega), fun hC g' hg' =>
        hch _ g' (hgs hC) hg', ?_⟩
    · intro w hw
      rw [length_layerChain_fst]
      simp only [List.mem_cons] at hw
      rcases hw with rfl | rfl | hw
      · simp; omega
      · simp; omega
      · have := layerChain_snd_lt hw
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        omega
    · rw [length_layerChain_fst]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- The column fold, structurally, after the old vertices `0, …, v - 1`: with
`s = (List.range v).foldl C.layerColumn ([], [])`, `s.2.length = v`, `s.1` is acyclic over the
`n + n` inputs, every column entry lies below `n + n + |s.1|`, every gate is a NAND gate when
`C.IsNANDForm`, and `s.1.length ≤ (2 * C.depth + 1) * v`.  Glue.

**Proof sketch.** Induction on `v` (`List.range_succ`, `List.foldl_append`), one step being
`layerColumn_struct`; the old columns stay in range because the gate list only grows
(`List.IsPrefix.length_le`). -/
private theorem DAGCircuit.layerFold_struct [NeZero n] (C : DAGCircuit n) (v : ℕ) :
    ((List.range v).foldl C.layerColumn ([], [])).2.length = v ∧
    GatesAcyclic (n + n) ((List.range v).foldl C.layerColumn ([], [])).1 ∧
    (∀ col ∈ ((List.range v).foldl C.layerColumn ([], [])).2, ∀ w ∈ col,
      w < n + n + ((List.range v).foldl C.layerColumn ([], [])).1.length) ∧
    (C.IsNANDForm → ∀ g ∈ ((List.range v).foldl C.layerColumn ([], [])).1, g.IsNAND) ∧
    ((List.range v).foldl C.layerColumn ([], [])).1.length ≤ (2 * C.depth + 1) * v := by
  induction v with
  | zero => exact ⟨rfl, GatesAcyclic.nil, by simp, by simp, by simp⟩
  | succ v ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range v).foldl C.layerColumn ([], []) = s at ih ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨⟨col, hc, hcw⟩, hp, ha, hn, hl⟩ := C.layerColumn_struct s v h2 h3 h4
    refine ⟨by rw [hc, List.length_append, h1]; rfl, ha, ?_, hn, ?_⟩
    · intro c hc' w hw
      rw [hc, List.mem_append, List.mem_singleton] at hc'
      rcases hc' with hc' | rfl
      · have := h3 c hc' w hw
        have := hp.length_le
        omega
      · exact hcw w hw
    · rw [Nat.mul_succ]
      omega

/-! ## The structure fields (targets) -/

/-- **N12. Acyclicity of the layering.** Every gate of `C.layerGates` reads only earlier vertices
of the circuit on `n + n` inputs: `∀ (i : ℕ) (h : i < C.layerGates.length),
∀ a ∈ (C.layerGates[i]).args, a < n + n + i` (the `args_lt` field of `DAGCircuit (n + n)`, i.e.
`GatesAcyclic (n + n) C.layerGates`).  Glue.

Stated in the field's form rather than as `GatesAcyclic (n + n) C.layerGates` (plan section r3
§H5.6b): `GatesAcyclic` (`DAGCircuit.lean`) has no published reader, and filling the field from a
`GatesAcyclic` proof would unfold it (Rule 10).  The meaning is identical (the body of
`GatesAcyclic`).

**Proof sketch.** Induction along the fold (`layerFold_eq`, `List.foldl` over `List.range`) with
the column invariant of the module docstring, part "every recorded copy lies below the current
vertex count": each step (`layerColumn_eq`) appends gates that read `n + v` or `0, n` (inputs,
below `n + n` by `NeZero n`), the recorded copies of earlier vertices (below the count by the
invariant; the arguments `a` of gate `v - n` satisfy `a < v` by `C.args_lt`), or the gates just
appended (`layerChain_succ`: the inner gate `N + |gs|` precedes the outer one).  Each appended
gate's arguments are therefore below its own vertex `n + n + i`. -/
theorem DAGCircuit.layerGates_acyclic [NeZero n] (C : DAGCircuit n) :
    ∀ (i : ℕ) (h : i < C.layerGates.length), ∀ a ∈ (C.layerGates[i]).args, a < n + n + i := by
  have h := (C.layerFold_struct (n + C.gates.length)).2.1
  rw [← layerFold_eq, ← layerGates_eq] at h
  exact gatesAcyclic_iff.mp h

/-- **N13. The output is a vertex.** `C.layerOutput < (n + n) + C.layerGates.length` (the
`output_lt` field of `DAGCircuit (n + n)`).  Glue.

**Proof sketch.** The output's column exists because `C.depthAt C.output = C.depth`
(`DAGCircuit.depth_eq`) and `C.output < n + C.gates.length` (`C.output_lt`), so the fold visits
it and does not take the dead branch; its first entry is `out@D` (`layerOutput_eq`,
`layerAt_eq`, index `D - D = 0`), which by the column invariant is below the vertex count
`n + n + |C.layerGates|`. -/
theorem DAGCircuit.layerOutput_lt [NeZero n] (C : DAGCircuit n) :
    C.layerOutput < (n + n) + C.layerGates.length := by
  have h := (C.layerFold_struct (n + C.gates.length)).2.2.1
  rw [← layerFold_eq, ← layerGates_eq] at h
  rw [layerOutput_eq]
  exact C.layerAt_lt (by have := Nat.pos_of_neZero n; omega) h _ _

/-! ## The conversion -/

/-- **The layering conversion** (plan section r3 §H3.13): the circuit on the `n + n` literal
inputs with gates `C.layerGates` and output `C.layerOutput`,
`C.layerNAND = ⟨C.layerGates, C.layerOutput, N12, N13⟩` (field readers `layerNAND_gates`,
`layerNAND_output`, generated by `simps`, not `@[simp]`).  While N12 and N13 are admitted,
`sorryAx` reaches it through them only.  Glue (no ingested source, r3 §H1 gap 4); motivated by
[BV11, Thm 3.1, p015-b001; Def 3.6, p014-b001]. -/
@[simps (config := { isSimp := false }) gates output]
def DAGCircuit.layerNAND [NeZero n] (C : DAGCircuit n) : DAGCircuit (n + n) where
  gates := C.layerGates
  output := C.layerOutput
  args_lt := C.layerGates_acyclic
  output_lt := C.layerOutput_lt

section LayerNAND

variable [NeZero n] (C : DAGCircuit n)

/-- **N7. Semantics on the literal input.** For a NAND-form circuit the layering computes the same
function on the literals: `C.IsNANDForm → C.layerNAND.eval (litInput x) = C.eval x`.  Glue.

**Proof sketch.** The column invariant, value part, at the output: by induction along the fold,
every recorded copy `v@k` has on `litInput x` the value of `v` on `x`.  Inputs: `v@0` is input
vertex `v` (`DAGCircuit.values_getD_input`, `litInput_castAdd`); the twin `NAND(¬xᵥ)` reads
vertex `n + v` (`litInput_natAdd`) and gives `!!xᵥ = xᵥ` (`DAGGate.eval_of_isNAND`, N1).
Gates: the old gate is a NAND gate (`DAGCircuit.isNANDForm_iff`, `DAGGate.eval_of_isNAND`) and
the base and twin read copies with the same values (`DAGCircuit.values_getD_gate`); a fan-in-0
twin gives `!(!(x₀ && !x₀)) = false`.  A chain link gives `!!b = b`.  Read off at
`out@D` with `DAGCircuit.eval_eq` and `layerNAND_output`. -/
theorem DAGCircuit.layerNAND_eval (hC : C.IsNANDForm) (x : Fin n → Bool) :
    C.layerNAND.eval (litInput x) = C.eval x := by
  sorry

/-- **N8. Layered.** `C.layerNAND.IsLayered`, with no hypothesis: every new gate reads only copies
one level down.  Glue.

**Proof sketch.** `isLayered_iff`, then the column invariant, depth part: every recorded copy
`v@k` has depth exactly `k` (`DAGCircuit.depthAt_gate`, `DAGGate.depth_eq`; the depth of a gate
does not depend on its kind, so no NAND-form hypothesis is needed), and every gate appended at
level `k` reads only vertices of depth `k - 1`: the base reads `a@(δ - 1)`, the twin `a@δ` (or
inputs `0, n` through the inner gate), a chain link `v@(k - 2)` through the inner gate at level
`k - 1`. -/
theorem DAGCircuit.layerNAND_isLayered : C.layerNAND.IsLayered := by
  sorry

/-- **N9. NAND form.** `C.IsNANDForm → C.layerNAND.IsNANDForm`: every gate is emitted as a `¬`
gate, and the copies keep the old fan-in, so `hC` is needed for fan-in `≤ 2`.  Glue.

**Proof sketch.** `isNANDForm_iff`, `DAGGate.isNAND_iff` and `layerNAND_gates`: induction along the
fold (`layerFold_eq`, `layerColumn_eq`, `layerChain_succ`); every appended gate is
`⟨.not, args⟩` with `args` of length `1` (chain, input twin), `2` (`NAND[0, n]`) or the old
gate's fan-in (base and twin, `List.length_map`), which is at most `2` by `hC`. -/
theorem DAGCircuit.layerNAND_isNANDForm (hC : C.IsNANDForm) : C.layerNAND.IsNANDForm := by
  sorry

/-- **N10. Depth is preserved exactly.** `C.layerNAND.depth = C.depth`.  Glue.

**Proof sketch.** `DAGCircuit.depth_eq` and `layerNAND_output`: the output is `out@D` with
`D = C.depth` (`layerOutput_eq`), and by the column invariant, depth part, it has depth exactly
`D`. -/
theorem DAGCircuit.layerNAND_depth : C.layerNAND.depth = C.depth := by
  sorry

/-- **N11. Size.** `C.layerNAND.size ≤ 2 * n + (2 * C.depth + 1) * C.size`.  Glue.

Constant settled at the statement phase: with `D = C.depth` and `δ = C.depthAt v`, the column of
an input has `0` gates (`D = 0`) or `1 + 2 (D - 1) = 2D - 1` (twin and chain); the column of a live
gate has `1` (base) when `δ = D`, otherwise `1 + 1 + 2 (D - δ - 1) = 2 (D - δ)` gates, or
`2 (D - δ) + 1` for a fan-in-0 gate (two-gate twin); a dead vertex has none.  Every column has at
most `2D + 1` gates, so `|C.layerGates| ≤ (2D + 1) (n + |C.gates|)`, and the size is
`(n + n) + |C.layerGates| ≤ 2n + (2D + 1) · C.size`.

**Proof sketch.** `DAGCircuit.size_eq` (both circuits) and `layerNAND_gates`; induction along the
fold with the column-length part of the invariant (each step appends at most `2D + 1` gates:
`layerColumn_eq`, `layerChain` appends exactly two gates per link), summed over the
`n + |C.gates|` old vertices. -/
theorem DAGCircuit.layerNAND_size_le : C.layerNAND.size ≤ 2 * n + (2 * C.depth + 1) * C.size := by
  sorry

end LayerNAND

end BoolCircuit
