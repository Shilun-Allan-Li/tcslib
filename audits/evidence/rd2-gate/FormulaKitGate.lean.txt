/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNFEncoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The machine-to-formula kit, part I: gates, layouts and ledgers

The formula half of item H6 of the host registry (`machine-library-design.md` §14): what a
reduction needs in order to write its CNF with **closed-form variable numbering** and
**explicitly ordered clause lists**, so that a polynomial-time emitter can be proved to output
that formula literally. The emission half is `TCSlib.Complexity.FormulaKit.Emit`.

## Design

* **Blocks.** Variables are laid out in consecutive blocks of a fixed width (`blockVar`): the
  snapshot packing of the Cook-Levin tableau [AB09, Lemma 2.11] and the level blocks of the
  `TQBF` reduction [AB09, Theorem 4.13] are both of this form.
* **Gates.** A local check of fixed arity `ℓ` is the truth-table **template** of its predicate
  [AB09, Claim 2.13], one excluding clause per falsifying row, the rows taken in the order
  `r = 0, …, 2^ℓ - 1` of their binary values, then relabeled by a wiring `ℕ → ℕ`. Deviation
  from `Complexity.exists_cnf_boolFun`: the clause list is an explicit function of the
  predicate (the private `falsifyingCNF` of `Formulas/CNF.lean` with its `Finset.univ` order
  replaced by `List.range` order), not a choice, so an emitter's output can be compared with it
  clause by clause. Repeated wire values are allowed.
* **Machine-constant data.** A reduction for a fixed machine may number the machine's finite
  types by a choice (an emitter for that machine stores the choice as a finite table). Anything
  that depends on the input length or a radius must be closed form. This is the line between
  the harmless choices of Cook-Levin (`CookLevin/Hardness.lean`) and the non-uniform numbering
  that design §16b item 2 retired from the `TQBF` codec.
* **Ledgers.** Sizes are counted by the clause-and-literal cost `cost` (empty clauses cost one
  unit), and bounded through the chapter-2 serialization (`Std.Sat.CNF.serialize`).

## Main definitions

* `Complexity.FormulaKit.blockVar` — variable `i` of block `t`.
* `Complexity.FormulaKit.template`, `Complexity.FormulaKit.gate` — the truth-table template of
  a fixed-arity predicate, and the template wired into the global numbering.
* `Complexity.FormulaKit.exactlyOne` — the exactly-one gadget over a list of variables.
* `Complexity.FormulaKit.cost` — the clause-and-literal cost.

## Main results

* `Complexity.FormulaKit.template_eval`, `Complexity.FormulaKit.gate_eval` — a gate computes
  its predicate on its wires. [AB09, Claim 2.13]
* `Complexity.FormulaKit.exactlyOne_eval` — exactly-one semantics.
* `Complexity.FormulaKit.serialize_length_le`, `Complexity.FormulaKit.gate_cost_le`,
  `Complexity.FormulaKit.exactlyOne_cost_le` — the size ledger.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Lemma 2.11, pp. 45-49; Claim 2.13, p. 46; Claim 4.4,
  pp. 80-81; Theorem 4.13, pp. 84-85.)
-/

namespace Complexity

namespace FormulaKit

open Std.Sat (CNF)

/-! ### Layouts and templates -/

/-- **Block variable**: the `i`-th variable of the `t`-th block of `width` consecutive
variables placed after `base` variables, that is `base + t · width + i`. The packing of the
snapshot variables of [AB09, Lemma 2.11] (Cook-Levin's private `clPack`), and the level-blocked
layout of the variables of [AB09, Theorem 4.13]'s formula `ψ`. -/
def blockVar (base width t i : ℕ) : ℕ := base + t * width + i

/-- The low `ℓ` bits of `r`, as an assignment to `Fin ℓ`: bit `i` is `r.testBit i`. -/
def bitsOf (ℓ r : ℕ) : Fin ℓ → Bool := fun i => r.testBit i.val

/-- The clause over the variables `0, …, ℓ - 1` that is false exactly at the assignment `v`
([AB09, Claim 2.13]): the literal on variable `i` has polarity `!v i`. -/
def excludeClause (ℓ : ℕ) (v : Fin ℓ → Bool) : CNF.Clause ℕ :=
  List.ofFn fun i => (i.val, !v i)

/-- **The truth-table template** of a predicate `p` of `ℓ` bits ([AB09, Claim 2.13]): one
excluding clause for every row on which `p` is false, the rows taken in the order
`r = 0, …, 2^ℓ - 1` of their binary values. Deviation from the private `clTemplate` of
`CookLevin/Hardness.lean` and `codecLocalCheck` of `ClassPSPACE/TQBF.lean`: the clause list is
an explicit function of `ℓ` and `p`, not a choice from `Complexity.exists_cnf_boolFun`. -/
def template (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) : CNF ℕ :=
  (List.range (2 ^ ℓ)).filterMap fun r =>
    if p (bitsOf ℓ r) then none else some (excludeClause ℓ (bitsOf ℓ r))

/-- **The template computes its predicate** ([AB09, Claim 2.13]): under any assignment `a`,
the template of `p` evaluates to `p` applied to `a`'s values on the variables `0, …, ℓ - 1`.

**Proof sketch.** The restriction of `a` to `Fin ℓ` is `bitsOf ℓ r` for the unique `r < 2^ℓ`
whose binary digits it lists (`Nat.testBit` of the sum of its powers of two). An excluding
clause is false at `a` exactly when its row is that restriction. So the template is false at
`a` iff that row was kept, that is iff `p` is false there. -/
theorem template_eval (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) (a : ℕ → Bool) :
    (template ℓ p).eval a = p (fun i => a i.val) := by
  sorry

/-- The template mentions only the variables `0, …, ℓ - 1`.

**Proof sketch.** Every literal of an excluding clause is on some `i.val` with `i : Fin ℓ`. -/
theorem template_numVars_le (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) :
    (template ℓ p).numVars ≤ ℓ := by
  sorry

/-- The template has at most one clause per row of the truth table, so at most `2^ℓ`
clauses.

**Proof sketch.** `List.filterMap` does not lengthen `List.range (2^ℓ)`. -/
theorem template_length_le (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) :
    (template ℓ p).length ≤ 2 ^ ℓ := by
  sorry

/-- Every clause of the template has exactly `ℓ` literals, so the template is an `ℓ`-CNF.

**Proof sketch.** Every clause is an `excludeClause ℓ _`, a `List.ofFn` over `Fin ℓ`. -/
theorem template_widthAtMost (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) :
    (template ℓ p).WidthAtMost ℓ := by
  sorry

/-- **A variable bound gives a `numVars` bound**: if every literal of `φ` is on a variable
below `N`, then `φ.numVars ≤ N`. (The public form of the private `foldr_max_le_of_forall` of
`Formulas/CNF.lean`, `numVars_le_of_literal_bounds` of `Formulas/CNFEncoding.lean` and
`codecCnf_numVars` of `ClassPSPACE/TQBF.lean`.)

**Proof sketch.** `Std.Sat.CNF.numVars` is the maximum fold of `v + 1` over the literals;
bound each term by `N` and use `List.max_le_of_forall_le`. -/
theorem numVars_le_of_forall_lt (φ : CNF ℕ) (N : ℕ) (h : ∀ C ∈ φ, ∀ l ∈ C, l.1 < N) :
    φ.numVars ≤ N := by
  sorry

/-- **A gate**: the template of `p` with its variable `j` wired to the global variable
`wire j`. Repeated wire values are allowed. The snapshot-keyed local gate of design §14
row H6: Cook-Levin's private `clGroup` and the configuration codec's
`Complexity.ConfigCodec.transitionGate` have this shape. -/
def gate (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) (wire : ℕ → ℕ) : CNF ℕ :=
  (template ℓ p).relabel wire

/-- **A gate computes its predicate on its wires**: under any assignment `a`, the gate
evaluates to `p` of the values `a (wire j)`, `j < ℓ`. (Proved: `template_eval` after
`Std.Sat.CNF.eval_relabel`.) -/
theorem gate_eval (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) (wire : ℕ → ℕ) (a : ℕ → Bool) :
    (gate ℓ p wire).eval a = p (fun i => a (wire i.val)) := by
  rw [gate, CNF.eval_relabel, template_eval]
  rfl

/-- The total read of an `ℓ`-bit assignment at a natural-number position: `v j` below `ℓ`,
and `false` at or above `ℓ`. (Lets a predicate be written over named ports numbered in
closed form.) -/
def readBit {ℓ : ℕ} (v : Fin ℓ → Bool) (j : ℕ) : Bool :=
  if h : j < ℓ then v ⟨j, h⟩ else false

/-! ### The exactly-one gadget -/

/-- **Exactly one of the listed variables is true**, without auxiliary variables: one
positive clause over the list and, for each ordered pair of distinct entries, one clause
excluding both. The clause order is the list order (the private `codecOneHot` of
`ClassPSPACE/TQBF.lean` took `Finset.univ.toList`, whose order is unspecified). -/
def exactlyOne (vs : List ℕ) : CNF ℕ :=
  [vs.map fun v => (v, true)] ++
    vs.flatMap fun v => (vs.filter fun w => w != v).map fun w => [(v, false), (w, false)]

/-- **Exactly-one semantics**: the gadget holds under `a` iff some listed variable `j` is
such that every listed variable `v` is true exactly when `v = j`. (Duplicates in the list are
harmless; the empty list gives the unsatisfiable gadget `[[]]`.)

**Proof sketch.** The positive clause supplies a true entry `j`; the exclusion clause of
`(j, v)` forces every listed `v ≠ j` false. Conversely a single true entry satisfies the
positive clause and every exclusion (the private `codecOneHot_eval`, over a list). -/
theorem exactlyOne_eval (vs : List ℕ) (a : ℕ → Bool) :
    (exactlyOne vs).eval a = true ↔ ∃ j ∈ vs, ∀ v ∈ vs, a v = decide (v = j) := by
  sorry

/-! ### Ledgers -/

/-- **The clause-and-literal cost** of a CNF: literal occurrences plus one per clause, so
that empty clauses are counted. (The private `codecCnfCost` of `ClassPSPACE/TQBF.lean`,
which RD-2a moves here.) -/
def cost {α : Type} (φ : CNF α) : ℕ := (φ.map fun C => C.length + 1).sum

/-- Renumbering variables preserves the cost. (Proved by unfolding.) -/
theorem cost_relabel {α β : Type} (φ : CNF α) (f : α → β) :
    cost (φ.relabel f) = cost φ := by
  simp [cost, CNF.relabel, CNF.Clause.relabel, List.map_map, Function.comp_def]

/-- Conjoining CNFs adds their costs. (Proved by unfolding.) -/
theorem cost_append {α : Type} (φ ψ : CNF α) : cost (φ ++ ψ) = cost φ + cost ψ := by
  simp [cost]

/-- A family of checks of cost at most `B` each costs at most its length times `B`.

**Proof sketch.** Induct on the family; `cost_append` at each step. -/
theorem cost_flatMap_le {α β : Type} (xs : List β) (f : β → CNF α) (B : ℕ)
    (h : ∀ x ∈ xs, cost (f x) ≤ B) : cost (xs.flatMap f) ≤ xs.length * B := by
  sorry

/-- **The serialization ledger**: if every variable of `φ` is below `N`, the chapter-2
serialization of `φ` has at most `cost φ · (N + 3) + 1` bits. (The private
`codecCnf_serialize` of `ClassPSPACE/TQBF.lean`, stated without the relabeling.)

**Proof sketch.** A literal below `N` serializes to at most `N + 2` bits; a clause adds its
marker and terminator, both charged to its extra cost unit; the formula adds one
terminator. -/
theorem serialize_length_le (φ : CNF ℕ) (N : ℕ) (h : ∀ C ∈ φ, ∀ l ∈ C, l.1 < N) :
    (CNF.serialize φ).length ≤ cost φ * (N + 3) + 1 := by
  sorry

/-- A gate costs at most `2^ℓ · (ℓ + 1)`, whatever its wiring.

**Proof sketch.** `cost_relabel`, then at most `2^ℓ` clauses (`template_length_le`) of
`ℓ` literals each (`template_widthAtMost`). -/
theorem gate_cost_le (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) (wire : ℕ → ℕ) :
    cost (gate ℓ p wire) ≤ 2 ^ ℓ * (ℓ + 1) := by
  sorry

/-- The exactly-one gadget over `m` listed variables costs at most `m + 1 + 3m²`.

**Proof sketch.** The positive clause costs `m + 1`; there are at most `m²` ordered pairs,
each excluded by one clause of cost `3`. -/
theorem exactlyOne_cost_le (vs : List ℕ) :
    cost (exactlyOne vs) ≤ vs.length + 1 + 3 * vs.length ^ 2 := by
  sorry

end FormulaKit

end Complexity
