/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.BranchingPrograms.Defs
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators

/-!
# Barrington's Theorem 2: branching programs to logarithmic-depth formulas

[Bar89, Thm 2]: a width-`w` branching program of length `l` is recognized by a fan-in-2 circuit
of depth `O(log l)`, the constant depending on `w`.  The circuit is built here as a fan-in-2
formula (`BoolCircuit.TreeCircuit`, P6-Q18) that mirrors the three sections of Bar89's proof:

1. *a constant-depth section per instruction* (`Instr.wire`): a map `f : [w] → [w]` is
   represented by the `w²` wires "`f(i) = j`", and for one instruction each wire is `true`,
   `false`, `x_var` or `¬x_var`;
2. *a binary tree of composition circuits* (`wireComp`, `compTree`): the wire
   `(g ∘ f)(i) = k` is `⋁_j (f(i) = j ∧ g(j) = k)`, a balanced fan-in-2 `∨`
   (`BoolCircuit.TreeCircuit.balanced`); the instruction list is split at its midpoint;
3. *a constant-depth acceptance section* (`toFormula`): `⋁_{f ∈ F} ⋀_i (B(x)(i) = f(i))`.

## Main definitions

* `BranchingProgram.Instr.wire`, `wireComp`, `compTree` — the sections 1 and 2.
* `BranchingProgram.toFormula` — the whole formula (`noncomputable`: it enumerates `F`).
* `BranchingProgram.topDepth` — the depth constant of the acceptance section.

## Main results

All are statements of the 6a statement phase (targets admitted with `sorry`), except the readers.

* `Instr.wire_eval`, `Instr.depth_wire_le`, `Instr.maxFanin_wire_le` (C17).
* `wireComp_eval`, `depth_wireComp_le` (C18).
* `compTree_eval`, `depth_compTree_le`, `maxFanin_compTree_le` (C19).
* `toFormula_eval` (C20), `depth_toFormula_le`, `maxFanin_toFormula_le` (C21).

## Deviations

* Bar89 builds a circuit; here it is a formula (fan-out one), of size `l^{O(log w)}`, polynomial
  for fixed `w` (`TreeCircuit.size_succ_le_two_pow`), as ruled by P6-Q18.  It reaches the
  `DAGCircuit` classes through `Language.InTreeNC.inNC` (`NC1.lean`).
* The depth constants, left implicit by Bar89, are explicit: `(⌈log₂ w⌉ + 2)·⌈log₂ l⌉ + 1` for the
  composition tree and `topDepth w = w·⌈log₂ w⌉ + ⌈log₂ w⌉ + 3` on top.

## References

* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1):150–164, 1989.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BranchingProgram

open BoolCircuit

variable {w n : ℕ}

/-! ### The constant-depth section per instruction -/

/-- The wire "`ι` sends `i` to `j`" as a formula of depth at most 1: `true` (`node true []`) if
both maps send `i` to `j`, the literal `¬x_var` if only `map0` does, `x_var` if only `map1` does,
and `false` (`node false []`) if neither,
`ι.wire i j = if ι.map0 i = j then (if ι.map1 i = j then node true [] else lit ⟨ι.var, false⟩)
else (if ι.map1 i = j then lit ⟨ι.var, true⟩ else node false [])`
[Bar89, Thm 2 proof, p004-b003: "a constant-depth section to find the function yielded by a each
instruction", sic]. -/
def Instr.wire (ι : Instr w n) (i j : Fin w) : TreeCircuit n :=
  if ι.map0 i = j then
    if ι.map1 i = j then .node true [] else .lit ⟨ι.var, false⟩
  else
    if ι.map1 i = j then .lit ⟨ι.var, true⟩ else .node false []

/-- Reader of `Instr.wire`: `ι.wire i j = if ι.map0 i = j then (if ι.map1 i = j then
node true [] else lit ⟨ι.var, false⟩) else (if ι.map1 i = j then lit ⟨ι.var, true⟩ else
node false [])`. -/
theorem Instr.wire_eq (ι : Instr w n) (i j : Fin w) :
    ι.wire i j =
      if ι.map0 i = j then
        (if ι.map1 i = j then .node true [] else .lit ⟨ι.var, false⟩)
      else
        (if ι.map1 i = j then .lit ⟨ι.var, true⟩ else .node false []) := rfl

/-! ### Composition circuits and the composition tree -/

/-- One composition circuit: from the wires `F i j` ("`f(i) = j`") and `G j k` ("`g(j) = k`"),
the wire "`(g ∘ f)(i) = k`" is the balanced fan-in-2 disjunction
`wireComp F G i k = balanced false [node true [F i j, G j k] | j ∈ finRange w]`
[Bar89, Thm 2 proof, p004-b003: "may be computed by a fixed circuit whose size depends only on
`w`"]. -/
def wireComp (F G : Fin w → Fin w → TreeCircuit n) : Fin w → Fin w → TreeCircuit n :=
  fun i k => TreeCircuit.balanced false ((List.finRange w).map fun j => .node true [F i j, G j k])

/-- Reader of `wireComp`:
`wireComp F G i k = balanced false ((finRange w).map fun j => node true [F i j, G j k])`. -/
theorem wireComp_eq (F G : Fin w → Fin w → TreeCircuit n) (i k : Fin w) :
    wireComp F G i k =
      TreeCircuit.balanced false ((List.finRange w).map fun j => .node true [F i j, G j k]) :=
  rfl

/-- The binary tree of composition circuits over an instruction list, split at the midpoint: the
empty list gives the identity wires (`node true []` on the diagonal, `node false []` off it), one
instruction gives its wires, and a list `l` of length at least 2 gives
`wireComp (compTree (l.take (|l| / 2))) (compTree (l.drop (|l| / 2)))` (the first half acts
first) [Bar89, Thm 2 proof, p004-b003: "a binary tree of composition circuits"].  Defined by
well-founded recursion on the length. -/
def compTree : List (Instr w n) → Fin w → Fin w → TreeCircuit n
  | [] => fun i j => if i = j then .node true [] else .node false []
  | [ι] => ι.wire
  | ι₁ :: ι₂ :: l =>
      wireComp (compTree ((ι₁ :: ι₂ :: l).take ((ι₁ :: ι₂ :: l).length / 2)))
        (compTree ((ι₁ :: ι₂ :: l).drop ((ι₁ :: ι₂ :: l).length / 2)))
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

/-- Reader of `compTree`, empty list: `compTree [] i j = if i = j then node true [] else
node false []`. -/
theorem compTree_nil (i j : Fin w) :
    compTree ([] : List (Instr w n)) i j =
      if i = j then .node true [] else .node false [] := by
  rw [compTree]

/-- Reader of `compTree`, one instruction: `compTree [ι] = ι.wire`. -/
theorem compTree_singleton (ι : Instr w n) : compTree [ι] = ι.wire := by
  rw [compTree]

/-- Reader of `compTree`, at least two instructions: with `l' = ι₁ :: ι₂ :: l`,
`compTree l' = wireComp (compTree (l'.take (l'.length / 2))) (compTree (l'.drop (l'.length / 2)))`.
-/
theorem compTree_cons_cons (ι₁ ι₂ : Instr w n) (l : List (Instr w n)) :
    compTree (ι₁ :: ι₂ :: l) =
      wireComp (compTree ((ι₁ :: ι₂ :: l).take ((ι₁ :: ι₂ :: l).length / 2)))
        (compTree ((ι₁ :: ι₂ :: l).drop ((ι₁ :: ι₂ :: l).length / 2))) := by
  rw [compTree]

/-! ### The acceptance section -/

/-- **Barrington's Theorem 2, one program** [Bar89, Thm 2, p004-b003]: the formula
`⋁_{f ∈ F} ⋀_i compTree B.instrs i (f i)` (the constant-depth acceptance section on top of the
composition tree), `B.toFormula F = balanced false [balanced true [compTree B.instrs i (f i) |
i ∈ finRange w] | f ∈ F.toList]`; it decides `B.yield x ∈ F` (C20).
Deviation: built as a formula (fan-out one), not a DAG (P6-Q18); `noncomputable`, because it
enumerates the `Finset` `F` (`Finset.toList`). -/
noncomputable def toFormula (B : BranchingProgram w n) (F : Finset (Fin w → Fin w)) :
    TreeCircuit n :=
  TreeCircuit.balanced false (F.toList.map fun f =>
    TreeCircuit.balanced true ((List.finRange w).map fun i => compTree B.instrs i (f i)))

/-- Reader of `toFormula`: `B.toFormula F = balanced false (F.toList.map fun f =>
balanced true ((finRange w).map fun i => compTree B.instrs i (f i)))`. -/
theorem toFormula_eq (B : BranchingProgram w n) (F : Finset (Fin w → Fin w)) :
    B.toFormula F = TreeCircuit.balanced false (F.toList.map fun f =>
      TreeCircuit.balanced true ((List.finRange w).map fun i => compTree B.instrs i (f i))) :=
  rfl

/-- The depth of the acceptance section for width `w`:
`topDepth w = w * Nat.clog 2 w + Nat.clog 2 w + 3` (one level for the leaves of the composition
tree, `⌈log₂ w⌉ + 1` for the `⋀_i`, `⌈log₂ |F|⌉ + 1 ≤ w·⌈log₂ w⌉ + 1` for the `⋁_f`, since
`|F| ≤ w^w`) [Bar89, Thm 2 proof, p004-b003: "a constant-depth section at the top"]. -/
def topDepth (w : ℕ) : ℕ :=
  w * Nat.clog 2 w + Nat.clog 2 w + 3

/-- Reader of `topDepth`: `topDepth w = w * Nat.clog 2 w + Nat.clog 2 w + 3`. -/
theorem topDepth_eq (w : ℕ) : topDepth w = w * Nat.clog 2 w + Nat.clog 2 w + 3 := rfl

/-! ### Targets C17–C21 -/

/-- **C17.** The wire of one instruction is correct: `(ι.wire i j).eval x =
decide (ι.eval x i = j)` [Bar89, Thm 2 proof, p004-b003].

**Proof sketch.** `Instr.wire_eq` and `Instr.eval_eq`; split on `ι.map0 i = j`, `ι.map1 i = j` and
`x ι.var`.  The constants evaluate by `TreeCircuit.eval_node_true_iff`/`eval_node_false_iff` on
`[]`, the literals by `TreeCircuit.eval_lit` and a reader of `Lit.eval` (missing at the base;
proposed `Lit.eval_eq : l.eval x = if l.sign then x l.idx else !x l.idx`). -/
theorem Instr.wire_eval (ι : Instr w n) (i j : Fin w) (x : Fin n → Bool) :
    (ι.wire i j).eval x = decide (ι.eval x i = j) := by
  sorry

/-- **C17.** The wire of one instruction has depth at most 1: `(ι.wire i j).depth ≤ 1`
[Bar89, Thm 2 proof, p004-b003: "constant-depth section"].

**Proof sketch.** `Instr.wire_eq`; an empty gate has depth 1 (`TreeCircuit.depth_node`,
`maxDepth_nil`) and a literal depth 0 (reader `TreeCircuit.depth_lit`, missing at the base and
proposed). -/
theorem Instr.depth_wire_le (ι : Instr w n) (i j : Fin w) : (ι.wire i j).depth ≤ 1 := by
  sorry

/-- **C17.** The wire of one instruction has fan-in at most 2: `(ι.wire i j).maxFanin ≤ 2`.  Glue.

**Proof sketch.** `Instr.wire_eq`; an empty gate has fan-in 0 (`TreeCircuit.maxFanin_node`,
`maxFaninL_nil`) and a literal fan-in 0 (reader `TreeCircuit.maxFanin_lit`, missing at the base
and proposed). -/
theorem Instr.maxFanin_wire_le (ι : Instr w n) (i j : Fin w) : (ι.wire i j).maxFanin ≤ 2 := by
  sorry

/-- **C18.** One composition circuit composes: if the wires `F` represent `f x` and the wires `G`
represent `g x`, then `(wireComp F G i k).eval x = decide (g x (f x i) = k)`
[Bar89, Thm 2 proof, p004-b003].

**Proof sketch.** `wireComp_eq`, `TreeCircuit.balanced_eval`, `eval_node_false` (an `any` over
`finRange w`) and `eval_node_true` on the pairs; by `hF`, `hG` the pair `j` is true iff
`f x i = j ∧ g x j = k`, and exactly `j = f x i` can be (`List.mem_finRange`). -/
theorem wireComp_eval {F G : Fin w → Fin w → TreeCircuit n}
    {f g : (Fin n → Bool) → Fin w → Fin w}
    (hF : ∀ x i j, (F i j).eval x = decide (f x i = j))
    (hG : ∀ x i j, (G i j).eval x = decide (g x i = j)) (i k : Fin w) (x : Fin n → Bool) :
    (wireComp F G i k).eval x = decide (g x (f x i) = k) := by
  sorry

/-- **C18.** A composition circuit adds `⌈log₂ w⌉ + 2` levels: if all wires of `F` and `G` have
depth `≤ d`, then `(wireComp F G i k).depth ≤ d + Nat.clog 2 w + 2` [Bar89, Thm 2 proof, p004-b003].

**Proof sketch.** `wireComp_eq` and `TreeCircuit.depth_balanced_le`: each `node true [F i j, G j k]`
has depth `≤ d + 1` (`depth_node`, `maxDepth_cons`), the list has length `w`
(`List.length_map`, `List.length_finRange`), so the depth is `≤ (d + 1) + ⌈log₂ w⌉ + 1`. -/
theorem depth_wireComp_le {F G : Fin w → Fin w → TreeCircuit n} {d : ℕ}
    (hF : ∀ i j, (F i j).depth ≤ d) (hG : ∀ i j, (G i j).depth ≤ d) (i k : Fin w) :
    (wireComp F G i k).depth ≤ d + Nat.clog 2 w + 2 := by
  sorry

/-- **C19.** The composition tree computes the yield: `(compTree B.instrs i j).eval x =
decide (B.yield x i = j)` [Bar89, Thm 2 proof, p004-b003].

**Proof sketch.** Strong induction on the length of an instruction list `l`, for the yield of
`⟨l⟩`: the empty list by `compTree_nil` and `yield_nil`; one instruction by `compTree_singleton`,
`Instr.wire_eval` and `yield_eq`; otherwise `compTree_cons_cons`, `wireComp_eval` with the
induction hypothesis for both halves, and `yield_append` on `l = l.take m ++ l.drop m`
(`List.take_append_drop`, `append_instrs`). -/
theorem compTree_eval (B : BranchingProgram w n) (i j : Fin w) (x : Fin n → Bool) :
    (compTree B.instrs i j).eval x = decide (B.yield x i = j) := by
  sorry

/-- **C19.** The composition tree has depth `O(log l)`:
`(compTree B.instrs i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1`
[Bar89, Thm 2 proof, p004-b003].
Constant (fixed at the statement phase): the leaves have depth `≤ 1` (identity wires and
`Instr.wire`), and a list of length `l ≥ 2` splits into halves of lengths `⌊l/2⌋ ≤ ⌈l/2⌉` with
`⌈log₂ ⌈l/2⌉⌉ = ⌈log₂ l⌉ − 1`, each split adding `⌈log₂ w⌉ + 2` levels (C18).

**Proof sketch.** Strong induction on the length `l` of the instruction list (with `length_eq`):
`compTree_nil`, `compTree_singleton` with `Instr.depth_wire_le` give depth `≤ 1`; for `l ≥ 2`,
`compTree_cons_cons` and `depth_wireComp_le` with the induction hypothesis for both halves
(`List.length_take`, `List.length_drop`), `Nat.clog_mono_right` and
`Nat.clog_of_two_le` (`⌈log₂ l⌉ = ⌈log₂ ⌈l/2⌉⌉ + 1`). -/
theorem depth_compTree_le (B : BranchingProgram w n) (i j : Fin w) :
    (compTree B.instrs i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1 := by
  sorry

/-- **C19.** The composition tree has fan-in at most 2: `(compTree B.instrs i j).maxFanin ≤ 2`.
Glue.

**Proof sketch.** Strong induction on the length as for `compTree_eval`: the leaves by
`compTree_nil` (`maxFanin_node`) and `Instr.maxFanin_wire_le`; a composition circuit by
`wireComp_eq`, `TreeCircuit.maxFanin_balanced_le` and `maxFanin_node` on the binary `∧` nodes. -/
theorem maxFanin_compTree_le (B : BranchingProgram w n) (i j : Fin w) :
    (compTree B.instrs i j).maxFanin ≤ 2 := by
  sorry

/-- **C20.** Barrington's Theorem 2 formula decides acceptance:
`(B.toFormula F).eval x = decide (B.yield x ∈ F)` [Bar89, Thm 2, p004-b003].

**Proof sketch.** `toFormula_eq`, `TreeCircuit.balanced_eval`, `eval_node_false` (an `any` over
`F.toList`, `Finset.mem_toList`) and `eval_node_true` (an `all` over `finRange w`); by
`compTree_eval` the conjunction for `f` holds iff `∀ i, B.yield x i = f i`, i.e.
`B.yield x = f` (`funext`). -/
theorem toFormula_eval (B : BranchingProgram w n) (F : Finset (Fin w → Fin w))
    (x : Fin n → Bool) : (B.toFormula F).eval x = decide (B.yield x ∈ F) := by
  sorry

/-- **C21.** Depth `O(log l)` with a constant depending on `w`:
`(B.toFormula F).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + topDepth w`
[Bar89, Thm 2, p004-b003: "depth `O(log l)`, where the constant depends on `w`"].
Constant (fixed at the statement phase): `topDepth w = w·⌈log₂ w⌉ + ⌈log₂ w⌉ + 3`; r3's draft
`+ 4` is one more than needed.

**Proof sketch.** `toFormula_eq` and `TreeCircuit.depth_balanced_le` twice.  The inner `⋀_i` over
`w` wires of depth `≤ T = (⌈log₂ w⌉ + 2)·⌈log₂ l⌉ + 1` (`depth_compTree_le`) has depth
`≤ T + ⌈log₂ w⌉ + 1`; the outer `⋁_f` over `|F| ≤ w^w` terms (`Finset.length_toList`,
`Finset.card_le_univ`, `Fintype.card_fun`) adds `⌈log₂ |F|⌉ + 1 ≤ w·⌈log₂ w⌉ + 1`
(`Nat.clog_mono_right`, `Nat.clog_le_of_le_pow` with `w^w ≤ (2^⌈log₂ w⌉)^w`, `Nat.le_pow_clog`);
`topDepth_eq` closes the arithmetic. -/
theorem depth_toFormula_le (B : BranchingProgram w n) (F : Finset (Fin w → Fin w)) :
    (B.toFormula F).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + topDepth w := by
  sorry

/-- **C21.** Barrington's Theorem 2 formula has fan-in at most 2: `(B.toFormula F).maxFanin ≤ 2`
[Bar89, Thm 2, p004-b003: "a fan-in 2 circuit"].

**Proof sketch.** `toFormula_eq`, `TreeCircuit.maxFanin_balanced_le` twice, and
`maxFanin_compTree_le` for the leaves (`maxFaninL` of a mapped list). -/
theorem maxFanin_toFormula_le (B : BranchingProgram w n) (F : Finset (Fin w → Fin w)) :
    (B.toFormula F).maxFanin ≤ 2 := by
  sorry

end BranchingProgram
