/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
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
  rw [DAGGate.eval_eq, ((DAGGate.isNAND_iff g).mp hg).1]

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

/-! ## Correctness of the NAND gadget -/

/-- Glue: the depth of an existing vertex `v < n + gs.length` of a gate list is its entry in
the depth run, `vertexDepth n gs v = (runWith DAGGate.depth gs (List.replicate n 0)).getD v 0`.
Derived from the published readers `vertexDepth_input`, `vertexDepth_append`,
`vertexDepth_last` (`TreeDAG.lean`) and `runWith_getD_of_lt`, `runWith_getD_gate`
(`DAGCircuit.lean`), without unfolding `vertexDepth`, which has no `_eq` reader (an owner-side
`vertexDepth_eq` would replace this lemma).

**Proof sketch.** An input vertex `v < n` has depth `0` on both sides.  A gate vertex `n + j`
keeps its depth when the gates after it are dropped, so both sides are the depth of gate `j`
over the depth run of the first `j` gates. -/
private theorem vertexDepth_eq_getD (gs : List DAGGate) {v : ℕ} (hv : v < n + gs.length) :
    vertexDepth n gs v = (runWith DAGGate.depth gs (List.replicate n 0)).getD v 0 := by
  by_cases hvn : v < n
  · rw [vertexDepth_input gs hvn,
      runWith_getD_of_lt _ _ _ (by rwa [List.length_replicate]), List.getD_replicate _ hvn]
  · obtain ⟨j, rfl⟩ : ∃ j, v = n + j := ⟨v - n, by omega⟩
    have hj : j < gs.length := by omega
    have hgate := runWith_getD_gate DAGGate.depth gs (List.replicate n 0) hj 0
    have hlast := vertexDepth_last (n := n) (gs.take j) gs[j]
    rw [List.length_replicate] at hgate
    rw [List.length_take_of_le hj.le, List.take_concat_get' gs j hj] at hlast
    rw [hgate, ← hlast]
    conv_lhs => rw [← List.take_append_drop (j + 1) gs]
    exact vertexDepth_append _ _ (by rw [List.length_take_of_le hj]; omega)

/-- Glue: a gate reading only existing vertices of `gs` has, over the depth run of `gs`, one
level more than its deepest argument:
`g.depth (runWith DAGGate.depth gs (List.replicate n 0)) =
1 + (g.args.map (vertexDepth n gs)).foldr max 0`, by `DAGGate.depth_eq` and
`vertexDepth_eq_getD` on each argument. -/
private theorem depth_runWith_eq {g : DAGGate} {gs : List DAGGate}
    (hg : ∀ a ∈ g.args, a < n + gs.length) :
    g.depth (runWith DAGGate.depth gs (List.replicate n 0)) =
      1 + (g.args.map (vertexDepth n gs)).foldr max 0 := by
  rw [DAGGate.depth_eq, List.map_congr_left fun a ha => (vertexDepth_eq_getD gs (hg a ha)).symm]

/-- Glue: a one-gate gadget.  Emitting a single NAND gate `g₁` that reads the arguments of `g`
and computes `g` meets `GadgetSpec` with depth factor `2`:
`GadgetSpec n 2 (g.args.length + 2) DAGGate.IsNAND g gs (gs ++ [g₁], n + gs.length)`.  It
covers the copied `¬` gate and `∨[] ↦ NAND[]`.

**Proof sketch.** The new vertex is the last one, so its value and depth are `g₁`'s over the
run of `gs` (`vertexValue_last`, `vertexDepth_last`); `depth_runWith_eq` gives one level over
the deepest argument. -/
private theorem gadgetSpec_single {g g₁ : DAGGate} {gs : List DAGGate} (hgs : GatesAcyclic n gs)
    (hargs : ∀ a ∈ g.args, a < n + gs.length) (hg₁ : g₁.IsNAND) (hga : g₁.args = g.args)
    (hval : ∀ vals, g₁.eval vals = g.eval vals) :
    GadgetSpec n 2 (g.args.length + 2) DAGGate.IsNAND g gs (gs ++ [g₁], n + gs.length) := by
  have hargs₁ : ∀ a ∈ g₁.args, a < n + gs.length := hga ▸ hargs
  refine ⟨⟨[g₁], rfl⟩, hgs.snoc hargs₁, ?_, fun x => ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · exact (vertexValue_last gs g₁ x).trans (hval _)
  · simp only [List.length_append, List.length_singleton]; omega
  · show vertexDepth n (gs ++ [g₁]) (n + gs.length) ≤ _
    rw [vertexDepth_last, depth_runWith_eq hargs₁, hga]
    omega
  · intro h hh
    simp only [List.drop_left, List.mem_singleton] at hh
    exact hh ▸ hg₁

/-- Glue: a two-gate gadget.  Emitting a NAND gate `g₁` that reads the arguments of `g` and
computes `¬g`, then its negation `NAND[g₁]`, meets `GadgetSpec` with depth factor `2`:
`GadgetSpec n 2 (g.args.length + 2) DAGGate.IsNAND g gs
(gs ++ [g₁, ⟨.not, [n + gs.length]⟩], n + gs.length + 1)`.  It covers `∧[]`, `∧[a]`, `∨[a]`
and `∧[a, b]`.

**Proof sketch.** The output vertex is the last one: its value is `¬` of vertex
`n + |gs|`, which is `g₁`'s value over the run of `gs` (`vertexValue_last`,
`runWith_getD_last`), hence `g`'s by `hval`.  Its depth is one more than `g₁`'s, which is one
more than the deepest argument (`depth_runWith_eq`). -/
private theorem gadgetSpec_double {g g₁ : DAGGate} {gs : List DAGGate} (hgs : GatesAcyclic n gs)
    (hargs : ∀ a ∈ g.args, a < n + gs.length) (hg₁ : g₁.IsNAND) (hga : g₁.args = g.args)
    (hval : ∀ vals, (!g₁.eval vals) = g.eval vals) :
    GadgetSpec n 2 (g.args.length + 2) DAGGate.IsNAND g gs
      (gs ++ [g₁, ⟨.not, [n + gs.length]⟩], n + gs.length + 1) := by
  have hargs₁ : ∀ a ∈ g₁.args, a < n + gs.length := hga ▸ hargs
  have e : gs ++ [g₁, ⟨.not, [n + gs.length]⟩] = gs ++ [g₁] ++ [⟨.not, [n + gs.length]⟩] := by
    rw [List.append_assoc]; rfl
  have hl₁ : (gs ++ [g₁]).length = gs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hm : n + gs.length + 1 = n + (gs ++ [g₁]).length := by rw [hl₁]; omega
  have h₂ : (⟨.not, [n + gs.length]⟩ : DAGGate).IsNAND :=
    (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
  refine ⟨⟨[g₁, ⟨.not, [n + gs.length]⟩], rfl⟩, ?_, ?_, fun x => ?_, ?_, ?_, ?_⟩
  · rw [e]
    refine (hgs.snoc hargs₁).snoc fun a ha => ?_
    rw [List.mem_singleton.mp ha, hl₁]
    omega
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · -- value: the output negates vertex `n + |gs|`, which computes `¬g`
    have hlast := runWith_getD_last DAGGate.eval gs g₁ (List.ofFn x) false
    rw [List.length_ofFn] at hlast
    show vertexValue (gs ++ [g₁, ⟨.not, [n + gs.length]⟩]) x (n + gs.length + 1) = _
    rw [e, hm, vertexValue_last, DAGGate.eval_of_isNAND h₂, List.all_cons, List.all_nil,
      Bool.and_true, hlast, hval]
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · -- depth: one level over `g₁`, which is one level over the deepest argument
    have hlast := runWith_getD_last DAGGate.depth gs g₁ (List.replicate n 0) 0
    rw [List.length_replicate, depth_runWith_eq hargs₁, hga] at hlast
    show vertexDepth n (gs ++ [g₁, ⟨.not, [n + gs.length]⟩]) (n + gs.length + 1) ≤ _
    rw [e, hm, vertexDepth_last, DAGGate.depth_eq, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, hlast]
    omega
  · intro h hh
    simp only [List.drop_left, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact hg₁
    · exact h₂

/-- Glue: the three-gate gadget of `∨[a, b]`, `NAND[a]`, `NAND[b]`, `NAND[¬a, ¬b]`, meets
`GadgetSpec` with depth factor `2`:
`GadgetSpec n 2 4 DAGGate.IsNAND ⟨.or, [a, b]⟩ gs (nandGadget n ⟨.or, [a, b]⟩ gs)`, written
out by `nandGadget_or_pair`.

**Proof sketch.** De Morgan: the output is `¬(¬a ∧ ¬b) = a ∨ b`.  The two negations sit at
vertices `n + |gs|` and `n + |gs| + 1` and read only old vertices, whose values and depths
the later gates do not change (`runWith_append`, `runWith_getD_of_lt`); each new vertex is
evaluated by `runWith_getD_last` and `DAGGate.eval_of_isNAND`, and its depth by
`depth_runWith_eq`.  The output is two levels above the deeper of `a`, `b`. -/
private theorem gadgetSpec_orPair {a b : ℕ} {gs : List DAGGate} (hgs : GatesAcyclic n gs)
    (hargs : ∀ v ∈ (⟨.or, [a, b]⟩ : DAGGate).args, v < n + gs.length) :
    GadgetSpec n 2 ((⟨.or, [a, b]⟩ : DAGGate).args.length + 2) DAGGate.IsNAND ⟨.or, [a, b]⟩ gs
      (gs ++ [⟨.not, [a]⟩, ⟨.not, [b]⟩, ⟨.not, [n + gs.length, n + gs.length + 1]⟩],
        n + gs.length + 2) := by
  have ha : a < n + gs.length := hargs a (by simp)
  have hb : b < n + gs.length := hargs b (by simp)
  have hN : ∀ l : List ℕ, l.length ≤ 2 → (⟨.not, l⟩ : DAGGate).IsNAND := fun l hl =>
    (DAGGate.isNAND_iff _).mpr ⟨rfl, hl⟩
  -- the three new gates, and the gate lists after one and two of them
  set g₁ : DAGGate := ⟨.not, [a]⟩ with hg₁
  set g₂ : DAGGate := ⟨.not, [b]⟩ with hg₂
  set g₃ : DAGGate := ⟨.not, [n + gs.length, n + gs.length + 1]⟩ with hg₃
  have e : gs ++ [g₁, g₂, g₃] = gs ++ [g₁] ++ [g₂] ++ [g₃] := by
    simp only [List.append_assoc]; rfl
  have hl₁ : (gs ++ [g₁]).length = gs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hl₂ : (gs ++ [g₁] ++ [g₂]).length = gs.length + 2 := by
    rw [List.length_append, hl₁, List.length_singleton]
  have hm : n + gs.length + 2 = n + (gs ++ [g₁] ++ [g₂]).length := by rw [hl₂]; omega
  refine ⟨⟨[g₁, g₂, g₃], rfl⟩, ?_, ?_, fun x => ?_, ?_, ?_, ?_⟩
  · rw [e]
    refine ((hgs.snoc fun v hv => ?_).snoc fun v hv => ?_).snoc fun v hv => ?_
    · rw [List.mem_singleton.mp hv]; exact ha
    · rw [List.mem_singleton.mp hv, hl₁]; omega
    · simp only [hg₃, List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [hl₂]; omega
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · -- value: `¬(¬a ∧ ¬b) = a ∨ b`
    set V := runWith DAGGate.eval gs (List.ofFn x)
    set V₁ := runWith DAGGate.eval (gs ++ [g₁]) (List.ofFn x) with hV₁
    have h₁ : V₁.getD (n + gs.length) false = g₁.eval V := by
      have := runWith_getD_last DAGGate.eval gs g₁ (List.ofFn x) false
      rwa [List.length_ofFn] at this
    have h₂ : (runWith DAGGate.eval (gs ++ [g₁] ++ [g₂]) (List.ofFn x)).getD
        (n + gs.length + 1) false = g₂.eval V₁ := by
      have := runWith_getD_last DAGGate.eval (gs ++ [g₁]) g₂ (List.ofFn x) false
      rwa [List.length_ofFn, hl₁, ← Nat.add_assoc] at this
    have h₁₂ : (runWith DAGGate.eval (gs ++ [g₁] ++ [g₂]) (List.ofFn x)).getD
        (n + gs.length) false = V₁.getD (n + gs.length) false := by
      rw [runWith_append, runWith_getD_of_lt]
      rw [length_runWith, List.length_ofFn, hl₁]; omega
    have hb₁ : V₁.getD b false = V.getD b false := by
      rw [hV₁, runWith_append, runWith_getD_of_lt]
      rw [length_runWith, List.length_ofFn]; exact hb
    show vertexValue (gs ++ [g₁, g₂, g₃]) x (n + gs.length + 2) = _
    rw [e, hm, vertexValue_last, DAGGate.eval_of_isNAND (hN [n + gs.length, n + gs.length + 1]
      (by simp)), List.all_cons, List.all_cons, List.all_nil, Bool.and_true, h₁₂, h₁, h₂, hg₁, hg₂,
      DAGGate.eval_of_isNAND (hN [a] (by simp)), DAGGate.eval_of_isNAND (hN [b] (by simp))]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [hb₁, DAGGate.eval_eq]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    cases V.getD a false <;> cases V.getD b false <;> rfl
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · -- depth: two levels over the deeper of `a` and `b`
    have hd₁ : (runWith DAGGate.depth (gs ++ [g₁]) (List.replicate n 0)).getD (n + gs.length) 0
        = 1 + max (vertexDepth n gs a) 0 := by
      have := runWith_getD_last DAGGate.depth gs g₁ (List.replicate n 0) 0
      rw [List.length_replicate, depth_runWith_eq (by simpa [hg₁] using ha)] at this
      rw [this, hg₁, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    have hd₂ : (runWith DAGGate.depth (gs ++ [g₁] ++ [g₂]) (List.replicate n 0)).getD
        (n + gs.length + 1) 0 = 1 + max (vertexDepth n gs b) 0 := by
      have := runWith_getD_last DAGGate.depth (gs ++ [g₁]) g₂ (List.replicate n 0) 0
      rw [List.length_replicate, hl₁, ← Nat.add_assoc,
        depth_runWith_eq (by simp only [hg₂, List.mem_singleton]; rintro v rfl; rw [hl₁]; omega),
        hg₂, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        vertexDepth_append gs [g₁] hb] at this
      exact this
    have hd₁₂ : (runWith DAGGate.depth (gs ++ [g₁] ++ [g₂]) (List.replicate n 0)).getD
        (n + gs.length) 0 =
          (runWith DAGGate.depth (gs ++ [g₁]) (List.replicate n 0)).getD (n + gs.length) 0 := by
      rw [runWith_append, runWith_getD_of_lt]
      rw [length_runWith, List.length_replicate, hl₁]; omega
    show vertexDepth n (gs ++ [g₁, g₂, g₃]) (n + gs.length + 2) ≤ _
    rw [e, hm, vertexDepth_last, DAGGate.depth_eq, hg₃, List.map_cons, List.map_cons,
      List.map_nil, List.foldr_cons, List.foldr_cons, List.foldr_nil, hd₁₂, hd₁, hd₂]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    omega
  · intro h hh
    simp only [List.drop_left, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl
    · exact hN _ (by simp)
    · exact hN _ (by simp)
    · exact hN _ (by simp)

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
  rw [gadgetCorrect_iff]
  intro g gs hgs hargs hl
  obtain ⟨k, args⟩ := g
  have hl' : args.length ≤ 2 := hl
  have hN : ∀ l : List ℕ, l.length ≤ 2 → (⟨.not, l⟩ : DAGGate).IsNAND := fun l hl =>
    (DAGGate.isNAND_iff _).mpr ⟨rfl, hl⟩
  cases k with
  | not =>
    -- a `¬` gate is copied
    rw [nandGadget_not]
    exact gadgetSpec_single hgs hargs (hN args hl') rfl fun _ => rfl
  | and =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · -- `∧[]`: `NAND[]`, then its negation
      rw [nandGadget_and_nil]
      refine gadgetSpec_double hgs hargs (hN [] (by simp)) rfl fun vals => ?_
      rw [DAGGate.eval_eq, DAGGate.eval_eq]
      simp only [List.all_nil, Bool.not_not]
    · -- `∧[a]`: double negation
      rw [nandGadget_and_singleton]
      refine gadgetSpec_double hgs hargs (hN [a] (by simp)) rfl fun vals => ?_
      rw [DAGGate.eval_eq, DAGGate.eval_eq]
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_not]
    · -- `∧[a, b]`: `NAND[a, b]`, then its negation
      rw [nandGadget_and_pair]
      refine gadgetSpec_double hgs hargs (hN [a, b] (by simp)) rfl fun vals => ?_
      rw [DAGGate.eval_eq, DAGGate.eval_eq]
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_not]
    · simp only [List.length_cons] at hl'; omega
  | or =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · -- `∨[]`: `NAND[]` is the constant `false`
      rw [nandGadget_or_nil]
      refine gadgetSpec_single hgs hargs (hN [] (by simp)) rfl fun vals => ?_
      rw [DAGGate.eval_eq, DAGGate.eval_eq]
      simp only [List.all_nil, List.any_nil, Bool.not_true]
    · -- `∨[a]`: double negation
      rw [nandGadget_or_singleton]
      refine gadgetSpec_double hgs hargs (hN [a] (by simp)) rfl fun vals => ?_
      rw [DAGGate.eval_eq, DAGGate.eval_eq]
      simp only [List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true,
        Bool.or_false, Bool.not_not]
    · -- `∨[a, b]`: `NAND[¬a, ¬b]` (De Morgan), three gates
      rw [nandGadget_or_pair]
      exact gadgetSpec_orPair hgs hargs
    · simp only [List.length_cons] at hl'; omega

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
  rw [DAGCircuit.toNANDForm_eq]
  exact DAGCircuit.rewrite_eval C (nandGadget n) nandGadget_correct hC x

/-- **N4. Form.** The conversion is in NAND form: `(C.toNANDForm hC).IsNANDForm`.  Glue.

**Proof sketch.** `isNANDForm_iff` and `toNANDForm_eq`, then `DAGCircuit.rewrite_new_gates`
(`DAGTransform.lean`): every gate of a rewritten circuit satisfies the gadget's output
predicate, here `DAGGate.IsNAND`. -/
theorem DAGCircuit.toNANDForm_isNANDForm : (C.toNANDForm hC).IsNANDForm := by
  rw [DAGCircuit.isNANDForm_iff, DAGCircuit.toNANDForm_eq]
  exact DAGCircuit.rewrite_new_gates C (nandGadget n) nandGadget_correct hC

/-- **N5. Depth.** The conversion at most doubles the depth:
`(C.toNANDForm hC).depth ≤ 2 * C.depth`.  Glue.

**Proof sketch.** `toNANDForm_eq`, then `DAGCircuit.rewrite_depth_le` (`DAGTransform.lean`)
with the depth factor `c = 2` of N2. -/
theorem DAGCircuit.toNANDForm_depth_le : (C.toNANDForm hC).depth ≤ 2 * C.depth := by
  rw [DAGCircuit.toNANDForm_eq]
  exact DAGCircuit.rewrite_depth_le C (nandGadget n) nandGadget_correct hC

/-- **N6. Size.** The conversion has at most `n + 4 · #gates` vertices:
`(C.toNANDForm hC).size ≤ n + 4 * C.gates.length`.  This is the generic `rewrite` bound
(`fan-in + 2 ≤ 4` gates per old gate), not the tight `3 · #gates` (disclosed).  Glue.

**Proof sketch.** `DAGCircuit.size_eq` on both sides and `toNANDForm_eq`; then
`DAGCircuit.rewrite_length_le` (`DAGTransform.lean`) bounds the new gate count by
`∑_{g ∈ C.gates} (g.args.length + 2)`, and each summand is at most `4` by `hC`
(`List.sum_le_card_nsmul` or an induction on the gate list). -/
theorem DAGCircuit.toNANDForm_size_le : (C.toNANDForm hC).size ≤ n + 4 * C.gates.length := by
  have hlen := DAGCircuit.rewrite_length_le C (nandGadget n) nandGadget_correct hC
  -- every old gate costs at most `2 + 2 = 4` new gates
  have hsum : (C.gates.map fun g => g.args.length + 2).sum ≤ C.gates.length * 4 := by
    have := List.sum_le_card_nsmul (C.gates.map fun g => g.args.length + 2) 4 fun y hy => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
      have := hC g hg
      omega
    rwa [List.length_map, Nat.nsmul_eq_mul] at this
  rw [DAGCircuit.size_eq, DAGCircuit.toNANDForm_eq]
  omega

end ToNANDForm

end BoolCircuit
