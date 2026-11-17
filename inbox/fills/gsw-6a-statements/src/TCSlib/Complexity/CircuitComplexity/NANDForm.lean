/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.CircuitComplexity.DAGTransform

/-!
# NAND form of `DAGCircuit`s

A *NAND gate* of `BoolCircuit.DAGCircuit` is the model's own `¬` gate read with at most two
arguments: `DAGGate.eval` evaluates a `¬` gate as the **negated conjunction** of its arguments
(`DAGGate.eval_eq`), so `⟨.not, [a, b]⟩` is `NAND(a, b)`, `⟨.not, [a]⟩` is `¬a = NAND(a)` and
`⟨.not, []⟩` is the constant `false`, the negation of the empty conjunction.  A circuit is in
*NAND form* when every gate is a NAND gate (`BoolCircuit.DAGCircuit.IsNANDForm`).

The conversion `BoolCircuit.DAGCircuit.toNANDForm` takes every circuit whose gates read at most
two vertices to NAND form.  It is an instance of the gate-rewriting host
`BoolCircuit.DAGCircuit.rewrite` (`DAGTransform.lean`), with the gadget
`BoolCircuit.nandGadget`, built in the style of `BoolCircuit.deMorganGadget` (`DAGFanin.lean`):

| old gate | NAND gadget | gates | depth added |
|---|---|---|---|
| `∧[a, b]` | `t := NAND[a, b]`, `NAND[t]` | 2 | 2 |
| `∨[a, b]` | `NAND[a]`, `NAND[b]`, `NAND[¬a, ¬b]` | 3 | 2 |
| `∧[a]`, `∨[a]` | `NAND[a]`, `NAND[that]` | 2 | 2 |
| `∧[]` (true) | `f := NAND[]`, `NAND[f]` | 2 | 2 (absolute) |
| `∨[]` (false) | `NAND[]` | 1 | 1 (absolute) |
| `¬[…]` | copied | 1 | 1 |

Every gadget costs at most `fan-in + 2` gates and at most two levels, so the pass gives the
semantics, depth at most `2 · depth`, and at most `n + 4 · #gates` vertices.

**Disclosures.**
* NAND-form circuits are **not** `BoolCircuit.DAGCircuit.IsWellFormed`, which demands `¬` gates of
  fan-in exactly one; lemmas assuming well-formedness (`toTree_eval`, `deMorgan_*`,
  `binarize_*`) do not apply to them.
* The names avoid `NAnd`: `BoolCircuit.NAndCircuit` and `BoolCircuit.TreeCircuit.toNAnd`
  (`Basic.lean`) are the AND-rooted alternating normal form of the LMN development, not NAND
  gates.
* No ingested source states that `{NAND}` is a complete basis or gives a conversion; the
  conversion is glue, motivated by [BV14, Def 2.13, p008-b002] and [BV14, Thm 3.5, p014-b001]
  ("every Boolean NAND circuit").

## Main definitions

* `BoolCircuit.DAGGate.IsNAND` — a `¬` gate reading at most two vertices.
* `BoolCircuit.DAGCircuit.IsNANDForm` — every gate is a NAND gate.
* `BoolCircuit.nandGadget` — the NAND gadget of the table above.
* `BoolCircuit.DAGCircuit.toNANDForm` — `C.rewrite (nandGadget n) nandGadget_correct hC`.

## Main results

All are statement-phase targets (glue):
* `BoolCircuit.DAGGate.eval_of_isNAND` (N1) — a NAND gate is the negated conjunction.
* `BoolCircuit.nandGadget_correct` (N2) — the gadget meets `GadgetCorrect` with depth factor 2.
* `BoolCircuit.DAGCircuit.toNANDForm_eval`, `toNANDForm_isNANDForm`, `toNANDForm_depth_le`,
  `toNANDForm_size_le` (N3–N6) — semantics, form, depth `≤ 2 · depth`, size `≤ n + 4 · #gates`.

While N2 is admitted, `sorryAx` reaches `toNANDForm` (whose body passes `nandGadget_correct` to
`rewrite`) and its consumers through N2 alone.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-based FHE as secure as PKE*, ITCS 2014;
  ePrint 2013/541.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## NAND gates and NAND form -/

/-- A *NAND gate*: a `¬` gate (negated conjunction, `DAGGate.eval_eq`) reading at most two
vertices, `g.IsNAND ↔ g.kind = .not ∧ g.args.length ≤ 2`.  Fan-in 1 is negation and fan-in 0
the constant `false`.  Not `BoolCircuit.NAndCircuit` (`Basic.lean`, an AND-rooted normal form).
Glue; motivated by [BV14, Def 2.13, p008-b002; Thm 3.5, p014-b001]. -/
def DAGGate.IsNAND (g : DAGGate) : Prop := g.kind = .not ∧ g.args.length ≤ 2

/-- The NAND-gate predicate unfolded: `g.IsNAND ↔ g.kind = .not ∧ g.args.length ≤ 2`. -/
theorem DAGGate.isNAND_iff (g : DAGGate) : g.IsNAND ↔ g.kind = .not ∧ g.args.length ≤ 2 :=
  Iff.rfl

instance DAGGate.decidableIsNAND : DecidablePred DAGGate.IsNAND := fun g =>
  inferInstanceAs (Decidable (g.kind = .not ∧ g.args.length ≤ 2))

/-- A circuit is in *NAND form* when every gate is a NAND gate:
`C.IsNANDForm ↔ ∀ g ∈ C.gates, g.IsNAND`.  Such circuits are not `IsWellFormed`, which demands
fan-in-1 `¬` gates (disclosed).  Glue; motivated by [BV14, Def 2.13, p008-b002]. -/
def DAGCircuit.IsNANDForm (C : DAGCircuit n) : Prop := ∀ g ∈ C.gates, g.IsNAND

/-- NAND form unfolded: `C.IsNANDForm ↔ ∀ g ∈ C.gates, g.IsNAND`. -/
theorem DAGCircuit.isNANDForm_iff (C : DAGCircuit n) :
    C.IsNANDForm ↔ ∀ g ∈ C.gates, g.IsNAND :=
  Iff.rfl

instance DAGCircuit.decidableIsNANDForm (C : DAGCircuit n) : Decidable C.IsNANDForm :=
  inferInstanceAs (Decidable (∀ g ∈ C.gates, g.IsNAND))

/-- **N1. NAND semantics.** A NAND gate evaluates to the negated conjunction of the values it
reads: `g.IsNAND → g.eval vals = !(g.args.all fun a => vals.getD a false)`.  Glue (a reader of
`DAGGate.eval` on NAND gates).

**Proof sketch.** Rewrite with `DAGGate.eval_eq` (`DAGCircuit.lean`); the kind is `.not` by the
first component of `g.isNAND_iff`, so the match takes its `.not` branch. -/
theorem DAGGate.eval_of_isNAND {g : DAGGate} (hg : g.IsNAND) (vals : List Bool) :
    g.eval vals = !(g.args.all fun a => vals.getD a false) := by
  sorry

/-! ## The NAND gadget -/

/-- The NAND gadget, compiling the gate `g` after the gates `gs` (vertex `n + gs.length` is the
first new gate); it returns the new gate list and the vertex computing `g` (the table of the
module docstring):
* `¬[…]`: copied, `(gs ++ [g], n + |gs|)`;
* `∧[]`: `f := NAND[]`, `NAND[f]`; `∨[]`: `NAND[]`;
* `∧[a]`, `∨[a]`: `NAND[a]`, `NAND[that]`;
* `∧[a, b]`: `t := NAND[a, b]`, `NAND[t]`; `∨[a, b]`: `NAND[a]`, `NAND[b]`, `NAND[¬a, ¬b]`;
* an `∧`/`∨` gate of fan-in above two lies outside the gadget's domain (`nandGadget_correct`
  assumes fan-in `≤ 2`) and is copied.
Computable; glue, in the style of `deMorganGadget` (`DAGFanin.lean`). -/
def nandGadget (n : ℕ) (g : DAGGate) (gs : List DAGGate) : List DAGGate × ℕ :=
  match g.kind, g.args with
  | .not, _ => (gs ++ [g], n + gs.length)
  | .and, [] => (gs ++ [⟨.not, []⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)
  | .or, [] => (gs ++ [⟨.not, []⟩], n + gs.length)
  | .and, [a] => (gs ++ [⟨.not, [a]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)
  | .or, [a] => (gs ++ [⟨.not, [a]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)
  | .and, [a, b] => (gs ++ [⟨.not, [a, b]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)
  | .or, [a, b] =>
    (gs ++ [⟨.not, [a]⟩, ⟨.not, [b]⟩, ⟨.not, [n + gs.length, n + gs.length + 1]⟩],
      n + gs.length + 2)
  | .and, _ :: _ :: _ :: _ => (gs ++ [g], n + gs.length)
  | .or, _ :: _ :: _ :: _ => (gs ++ [g], n + gs.length)

/-- The NAND gadget copies a `¬` gate:
`nandGadget n ⟨.not, args⟩ gs = (gs ++ [⟨.not, args⟩], n + gs.length)`. -/
theorem nandGadget_not (args : List ℕ) (gs : List DAGGate) :
    nandGadget n ⟨.not, args⟩ gs = (gs ++ [⟨.not, args⟩], n + gs.length) := by
  cases args with
  | nil => rfl
  | cons a l => rfl

/-- The NAND gadget on the constant `∧[]` (true):
`nandGadget n ⟨.and, []⟩ gs =
(gs ++ [⟨.not, []⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)`. -/
theorem nandGadget_and_nil (gs : List DAGGate) :
    nandGadget n ⟨.and, []⟩ gs =
      (gs ++ [⟨.not, []⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1) := rfl

/-- The NAND gadget on the constant `∨[]` (false):
`nandGadget n ⟨.or, []⟩ gs = (gs ++ [⟨.not, []⟩], n + gs.length)`. -/
theorem nandGadget_or_nil (gs : List DAGGate) :
    nandGadget n ⟨.or, []⟩ gs = (gs ++ [⟨.not, []⟩], n + gs.length) := rfl

/-- The NAND gadget on a fan-in-1 `∧` gate (double negation):
`nandGadget n ⟨.and, [a]⟩ gs =
(gs ++ [⟨.not, [a]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)`. -/
theorem nandGadget_and_singleton (a : ℕ) (gs : List DAGGate) :
    nandGadget n ⟨.and, [a]⟩ gs =
      (gs ++ [⟨.not, [a]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1) := rfl

/-- The NAND gadget on a fan-in-1 `∨` gate (double negation):
`nandGadget n ⟨.or, [a]⟩ gs =
(gs ++ [⟨.not, [a]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)`. -/
theorem nandGadget_or_singleton (a : ℕ) (gs : List DAGGate) :
    nandGadget n ⟨.or, [a]⟩ gs =
      (gs ++ [⟨.not, [a]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1) := rfl

/-- The NAND gadget on a fan-in-2 `∧` gate:
`nandGadget n ⟨.and, [a, b]⟩ gs =
(gs ++ [⟨.not, [a, b]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)`. -/
theorem nandGadget_and_pair (a b : ℕ) (gs : List DAGGate) :
    nandGadget n ⟨.and, [a, b]⟩ gs =
      (gs ++ [⟨.not, [a, b]⟩, ⟨.not, [n + gs.length]⟩], n + gs.length + 1) := rfl

/-- The NAND gadget on a fan-in-2 `∨` gate (De Morgan):
`nandGadget n ⟨.or, [a, b]⟩ gs = (gs ++ [⟨.not, [a]⟩, ⟨.not, [b]⟩,
⟨.not, [n + gs.length, n + gs.length + 1]⟩], n + gs.length + 2)`. -/
theorem nandGadget_or_pair (a b : ℕ) (gs : List DAGGate) :
    nandGadget n ⟨.or, [a, b]⟩ gs =
      (gs ++ [⟨.not, [a]⟩, ⟨.not, [b]⟩, ⟨.not, [n + gs.length, n + gs.length + 1]⟩],
        n + gs.length + 2) := rfl

/-- Outside its domain the NAND gadget copies the gate: for an `∧` or `∨` gate with at least
three arguments, `nandGadget n ⟨k, a :: b :: c :: l⟩ gs = (gs ++ [⟨k, a :: b :: c :: l⟩],
n + gs.length)` (`k ≠ .not`). -/
theorem nandGadget_of_three_le {k : GateKind} (hk : k ≠ .not) (a b c : ℕ) (l : List ℕ)
    (gs : List DAGGate) :
    nandGadget n ⟨k, a :: b :: c :: l⟩ gs = (gs ++ [⟨k, a :: b :: c :: l⟩], n + gs.length) := by
  cases k with
  | and => rfl
  | or => rfl
  | not => exact absurd rfl hk

/-- **N2. The NAND gadget is correct.** In the sense of `GadgetCorrect` (`DAGTransform.lean`),
with depth factor `2`, domain "fan-in at most two" and output predicate `DAGGate.IsNAND`:
`GadgetCorrect n 2 (fun _ l => l ≤ 2) DAGGate.IsNAND (nandGadget n)`.  That is, for every gate
`g` of fan-in at most two whose arguments are existing vertices of an acyclic gate list `gs`,
`nandGadget n g gs` only appends to `gs`, stays acyclic, returns a vertex below the new length
that computes `g`, adds at most `g.args.length + 2` gates and at most `2` levels over `g`'s
deepest argument, and every appended gate is a NAND gate.  Glue (the table of the module
docstring).

**Proof sketch.** As `deMorganGadget_correct` (`DAGFanin.lean`): case on the kind and on the
argument list (`nandGadget_not`, `nandGadget_and_nil`, …, the case readers above), and in each
case check the seven fields of `GadgetSpec`.  Extension and length are immediate (`ext` is the
emitted suffix; 1, 2 or 3 gates, at most `fan-in + 2`).  Acyclicity is `GatesAcyclic.snoc`
once per emitted gate (each reads only `g`'s arguments, below `n + |gs|`, or the gates just
emitted).  Values: `vertexValue_last` and `vertexValue_append` reduce each new vertex to a gate
evaluation, `DAGGate.eval_of_isNAND` (N1) and `DAGGate.eval_eq` give `!(a && b)`, `!!a = a`,
`!(!a && !b) = a || b`, `!true = false`, `!false = true` (`Bool` equation lemmas).  Depths:
`vertexDepth_last`, `vertexDepth_append` and `DAGGate.depth_eq`: one level for a copied `¬` gate
or `NAND[]`, two for the others.  New gates are `.not` gates of fan-in at most two by
`DAGGate.isNAND_iff`.  The fill needs a reader for `GadgetCorrect`, which has none at the issue
base (the owner-side `gadgetCorrect_iff`, plan section r3 §H2). -/
theorem nandGadget_correct :
    GadgetCorrect n 2 (fun _ l => l ≤ 2) DAGGate.IsNAND (nandGadget n) := by
  sorry

/-! ## The conversion -/

/-- **The NAND form of a circuit** whose gates read at most two vertices: the gate-rewriting host
applied to the NAND gadget, `C.toNANDForm hC = C.rewrite (nandGadget n) nandGadget_correct hC`.
The domain is `∀ g ∈ C.gates, g.args.length ≤ 2` (not `IsFaninTwo`: a `¬` gate of fan-in two is
already a NAND gate and is copied).  While N2 is admitted, `sorryAx` reaches this definition
through `nandGadget_correct` only.  Glue; motivated by [BV14, Def 2.13, p008-b002;
Thm 3.5, p014-b001]. -/
def DAGCircuit.toNANDForm (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) :
    DAGCircuit n :=
  C.rewrite (nandGadget n) nandGadget_correct hC

/-- The NAND form unfolded:
`C.toNANDForm hC = C.rewrite (nandGadget n) nandGadget_correct hC`. -/
theorem DAGCircuit.toNANDForm_eq (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) :
    C.toNANDForm hC = C.rewrite (nandGadget n) nandGadget_correct hC := rfl

section ToNANDForm

variable (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.args.length ≤ 2)

/-- **N3. Semantics.** The NAND form computes the same function:
`(C.toNANDForm hC).eval x = C.eval x`.  Glue.

**Proof sketch.** `toNANDForm_eq`, then `DAGCircuit.rewrite_eval` (`DAGTransform.lean`) with the
gadget's correctness N2. -/
theorem DAGCircuit.toNANDForm_eval (x : Fin n → Bool) : (C.toNANDForm hC).eval x = C.eval x := by
  sorry

/-- **N4. Form.** The conversion is in NAND form: `(C.toNANDForm hC).IsNANDForm`.  Glue.

**Proof sketch.** `isNANDForm_iff` and `toNANDForm_eq`, then `DAGCircuit.rewrite_new_gates`
(`DAGTransform.lean`): every gate of a rewritten circuit satisfies the gadget's output
predicate, here `DAGGate.IsNAND`. -/
theorem DAGCircuit.toNANDForm_isNANDForm : (C.toNANDForm hC).IsNANDForm := by
  sorry

/-- **N5. Depth.** The conversion at most doubles the depth:
`(C.toNANDForm hC).depth ≤ 2 * C.depth`.  Glue.

**Proof sketch.** `toNANDForm_eq`, then `DAGCircuit.rewrite_depth_le` (`DAGTransform.lean`)
with the depth factor `c = 2` of N2. -/
theorem DAGCircuit.toNANDForm_depth_le : (C.toNANDForm hC).depth ≤ 2 * C.depth := by
  sorry

/-- **N6. Size.** The conversion has at most `n + 4 · #gates` vertices:
`(C.toNANDForm hC).size ≤ n + 4 * C.gates.length`.  This is the generic `rewrite` bound
(`fan-in + 2 ≤ 4` gates per old gate), not the tight `3 · #gates` (disclosed).  Glue.

**Proof sketch.** `DAGCircuit.size_eq` on both sides and `toNANDForm_eq`; then
`DAGCircuit.rewrite_length_le` (`DAGTransform.lean`) bounds the new gate count by
`∑_{g ∈ C.gates} (g.args.length + 2)`, and each summand is at most `4` by `hC`
(`List.sum_le_card_nsmul` or an induction on the gate list). -/
theorem DAGCircuit.toNANDForm_size_le : (C.toNANDForm hC).size ≤ n + 4 * C.gates.length := by
  sorry

end ToNANDForm

end BoolCircuit
