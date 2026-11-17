/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.BigOperators
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

All are statements of the 6a statement phase (targets proved here), except the readers.

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
`x ι.var`.  The empty gates are the constants (`TreeCircuit.const_eq`) and evaluate by
`TreeCircuit.const_eval`, the literals by `TreeCircuit.eval_lit` and the reader `Lit.eval_eq`. -/
theorem Instr.wire_eval (ι : Instr w n) (i j : Fin w) (x : Fin n → Bool) :
    (ι.wire i j).eval x = decide (ι.eval x i = j) := by
  rw [Instr.wire_eq, Instr.eval_eq]
  by_cases h0 : ι.map0 i = j <;> by_cases h1 : ι.map1 i = j <;> cases hx : x ι.var <;>
    simp only [h0, h1, hx, if_true, if_false, ← TreeCircuit.const_eq, TreeCircuit.const_eval,
      TreeCircuit.eval_lit, Lit.eval_eq, Bool.false_eq_true, Bool.not_false, Bool.not_true,
      decide_true, decide_false]

/-- **C17.** The wire of one instruction has depth at most 1: `(ι.wire i j).depth ≤ 1`
[Bar89, Thm 2 proof, p004-b003: "constant-depth section"].

**Proof sketch.** `Instr.wire_eq`; an empty gate is a constant (`TreeCircuit.const_eq`) of depth 1
(`TreeCircuit.depth_const`) and a literal has depth 0 (reader `TreeCircuit.depth_lit`). -/
theorem Instr.depth_wire_le (ι : Instr w n) (i j : Fin w) : (ι.wire i j).depth ≤ 1 := by
  rw [Instr.wire_eq]
  split_ifs
  all_goals first
    | (rw [← TreeCircuit.const_eq]; exact (TreeCircuit.depth_const _).le)
    | (rw [TreeCircuit.depth_lit]; exact Nat.zero_le 1)

/-- **C17.** The wire of one instruction has fan-in at most 2: `(ι.wire i j).maxFanin ≤ 2`.  Glue.

**Proof sketch.** `Instr.wire_eq`; an empty gate is a constant (`TreeCircuit.const_eq`) of fan-in 0
(`TreeCircuit.maxFanin_const`) and a literal has fan-in 0 (reader `TreeCircuit.maxFanin_lit`). -/
theorem Instr.maxFanin_wire_le (ι : Instr w n) (i j : Fin w) : (ι.wire i j).maxFanin ≤ 2 := by
  rw [Instr.wire_eq]
  split_ifs
  all_goals first
    | (rw [← TreeCircuit.const_eq, TreeCircuit.maxFanin_const]; exact Nat.zero_le 2)
    | (rw [TreeCircuit.maxFanin_lit]; exact Nat.zero_le 2)

/-- **C18.** One composition circuit composes: if the wires `F` represent `f x` and the wires `G`
represent `g x`, then `(wireComp F G i k).eval x = decide (g x (f x i) = k)`
[Bar89, Thm 2 proof, p004-b003].

**Proof sketch.** `wireComp_eq`, the pairs as `TreeCircuit.and2` (`and2_eq`),
`TreeCircuit.balanced_eval` and `eval_node_false_iff` (some pair is true, `List.mem_map`); by
`and2_eval`, `hF`, `hG` the pair `j` is true iff `f x i = j ∧ g x j = k`, and exactly `j = f x i`
can be (`List.mem_finRange`). -/
theorem wireComp_eval {F G : Fin w → Fin w → TreeCircuit n}
    {f g : (Fin n → Bool) → Fin w → Fin w}
    (hF : ∀ x i j, (F i j).eval x = decide (f x i = j))
    (hG : ∀ x i j, (G i j).eval x = decide (g x i = j)) (i k : Fin w) (x : Fin n → Bool) :
    (wireComp F G i k).eval x = decide (g x (f x i) = k) := by
  rw [wireComp_eq]
  simp only [← TreeCircuit.and2_eq]
  rw [TreeCircuit.balanced_eval, Bool.eq_iff_iff, TreeCircuit.eval_node_false_iff,
    decide_eq_true_iff]
  constructor
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    rw [TreeCircuit.and2_eval, hF, hG, Bool.and_eq_true, decide_eq_true_iff,
      decide_eq_true_iff] at hcx
    rw [hcx.1]
    exact hcx.2
  · intro h
    refine ⟨TreeCircuit.and2 (F i (f x i)) (G (f x i) k),
      List.mem_map.2 ⟨f x i, List.mem_finRange _, rfl⟩, ?_⟩
    rw [TreeCircuit.and2_eval, hF, hG, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact ⟨rfl, h⟩

/-- A uniform depth bound on the members bounds the maximum depth of a list: if
`∀ c ∈ cs, c.depth ≤ d`, then `TreeCircuit.maxDepth cs ≤ d`.  Glue. -/
private theorem maxDepth_le_of_forall {cs : List (TreeCircuit n)} {d : ℕ}
    (h : ∀ c ∈ cs, c.depth ≤ d) : TreeCircuit.maxDepth cs ≤ d := by
  induction cs with
  | nil => rw [TreeCircuit.maxDepth_nil]; exact Nat.zero_le d
  | cons c cs ih =>
    rw [TreeCircuit.maxDepth_cons]
    exact max_le (h c List.mem_cons_self) (ih fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- A uniform fan-in bound on the members bounds the maximum fan-in of a list: if
`∀ c ∈ cs, c.maxFanin ≤ d`, then `TreeCircuit.maxFaninL cs ≤ d`.  Glue. -/
private theorem maxFaninL_le_of_forall {cs : List (TreeCircuit n)} {d : ℕ}
    (h : ∀ c ∈ cs, c.maxFanin ≤ d) : TreeCircuit.maxFaninL cs ≤ d := by
  induction cs with
  | nil => rw [TreeCircuit.maxFaninL_nil]; exact Nat.zero_le d
  | cons c cs ih =>
    rw [TreeCircuit.maxFaninL_cons]
    exact max_le (h c List.mem_cons_self) (ih fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- **C18.** A composition circuit adds `⌈log₂ w⌉ + 2` levels: if all wires of `F` and `G` have
depth `≤ d`, then `(wireComp F G i k).depth ≤ d + Nat.clog 2 w + 2` [Bar89, Thm 2 proof, p004-b003].

**Proof sketch.** `wireComp_eq` and `TreeCircuit.depth_balanced_le`: each pair
`node true [F i j, G j k] = and2 (F i j) (G j k)` has depth `≤ d + 1` (`depth_and2_le`), so the list
has `maxDepth ≤ d + 1` (`maxDepth_le_of_forall`), and it has length `w` (`List.length_map`,
`List.length_finRange`), so the depth is `≤ (d + 1) + ⌈log₂ w⌉ + 1`. -/
theorem depth_wireComp_le {F G : Fin w → Fin w → TreeCircuit n} {d : ℕ}
    (hF : ∀ i j, (F i j).depth ≤ d) (hG : ∀ i j, (G i j).depth ≤ d) (i k : Fin w) :
    (wireComp F G i k).depth ≤ d + Nat.clog 2 w + 2 := by
  rw [wireComp_eq]
  simp only [← TreeCircuit.and2_eq]
  refine (TreeCircuit.depth_balanced_le _ _).trans ?_
  rw [List.length_map, List.length_finRange]
  have hm : TreeCircuit.maxDepth ((List.finRange w).map fun j =>
      TreeCircuit.and2 (F i j) (G j k)) ≤ d + 1 := by
    refine maxDepth_le_of_forall fun c hc => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
    have h2 := TreeCircuit.depth_and2_le (F i j) (G j k)
    have h3 := hF i j
    have h4 := hG j k
    omega
  omega

/-- A composition circuit of fan-in-2 wires has fan-in 2: if `∀ i j, (F i j).maxFanin ≤ 2` and
`∀ i j, (G i j).maxFanin ≤ 2`, then `(wireComp F G i k).maxFanin ≤ 2`.  Glue. -/
private theorem maxFanin_wireComp_le {F G : Fin w → Fin w → TreeCircuit n}
    (hF : ∀ i j, (F i j).maxFanin ≤ 2) (hG : ∀ i j, (G i j).maxFanin ≤ 2) (i k : Fin w) :
    (wireComp F G i k).maxFanin ≤ 2 := by
  rw [wireComp_eq]
  simp only [← TreeCircuit.and2_eq]
  refine (TreeCircuit.maxFanin_balanced_le _ _).trans
    (max_le le_rfl (maxFaninL_le_of_forall fun c hc => ?_))
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  have h2 := TreeCircuit.maxFanin_and2_le (F i j) (G j k)
  have h3 := hF i j
  have h4 := hG j k
  omega

/-- The composition tree of an instruction list `l` computes the yield of the program `⟨l⟩`:
`(compTree l i j).eval x = decide ((⟨l⟩ : BranchingProgram w n).yield x i = j)`.  Glue.

**Proof sketch.** Well-founded recursion on `l.length`, following `compTree`.  Empty list:
`compTree_nil`, `const_eq`/`const_eval` and `yield_nil`.  One instruction: `compTree_singleton`,
`Instr.wire_eval`, and `yield_eq` with `List.foldl` on `[ι]`.  Otherwise (Step 1) `⟨l⟩` is
`⟨l.take m⟩ ++ ⟨l.drop m⟩` (`append_instrs`, `List.take_append_drop`), so (Step 2)
`compTree_cons_cons`, `yield_append` and `wireComp_eval` with the recursive calls close it. -/
private theorem compTree_eval_list :
    ∀ (l : List (Instr w n)) (x : Fin n → Bool) (i j : Fin w),
      (compTree l i j).eval x = decide ((⟨l⟩ : BranchingProgram w n).yield x i = j)
  | [], x, i, j => by
    rw [compTree_nil, yield_nil, id_eq]
    by_cases h : i = j
    · rw [if_pos h, ← TreeCircuit.const_eq, TreeCircuit.const_eval]
      exact (decide_eq_true h).symm
    · rw [if_neg h, ← TreeCircuit.const_eq, TreeCircuit.const_eval]
      exact (decide_eq_false h).symm
  | [ι], x, i, j => by
    have hy : (⟨[ι]⟩ : BranchingProgram w n).yield x = ι.eval x := by
      simp only [yield_eq, List.foldl_cons, List.foldl_nil, Function.comp_id]
    rw [compTree_singleton, Instr.wire_eval, hy]
  | ι₁ :: ι₂ :: l, x, i, j => by
    -- Step 1: the program is the concatenation of its two halves.
    have hsplit : ∀ (m : ℕ) (l' : List (Instr w n)),
        (⟨l'⟩ : BranchingProgram w n) = ⟨l'.take m⟩ ++ ⟨l'.drop m⟩ := by
      intro m l'
      have h : (⟨l'.take m⟩ ++ ⟨l'.drop m⟩ : BranchingProgram w n).instrs = l' := by
        rw [append_instrs]
        exact List.take_append_drop m l'
      exact (congrArg BranchingProgram.mk h).symm
    -- Step 2: compose the two halves.
    rw [compTree_cons_cons, hsplit ((ι₁ :: ι₂ :: l).length / 2) (ι₁ :: ι₂ :: l), yield_append]
    exact wireComp_eval
      (fun x i j => compTree_eval_list ((ι₁ :: ι₂ :: l).take ((ι₁ :: ι₂ :: l).length / 2)) x i j)
      (fun x i j => compTree_eval_list ((ι₁ :: ι₂ :: l).drop ((ι₁ :: ι₂ :: l).length / 2)) x i j)
      i j x
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

/-- **C19.** The composition tree computes the yield: `(compTree B.instrs i j).eval x =
decide (B.yield x i = j)` [Bar89, Thm 2 proof, p004-b003].

**Proof sketch.** The helper `compTree_eval_list`, for an arbitrary instruction list `l` and the
yield of `⟨l⟩`, by well-founded recursion on the length of `l` (as `compTree` itself): the empty
list by `compTree_nil`, `const_eval` and `yield_nil`; one instruction by `compTree_singleton`,
`Instr.wire_eval` and `yield_eq`; otherwise `compTree_cons_cons`, `wireComp_eval` with the
recursive calls for both halves, and `yield_append` on `⟨l⟩ = ⟨l.take m⟩ ++ ⟨l.drop m⟩`
(`List.take_append_drop`, `append_instrs`); then `l = B.instrs`. -/
theorem compTree_eval (B : BranchingProgram w n) (i j : Fin w) (x : Fin n → Bool) :
    (compTree B.instrs i j).eval x = decide (B.yield x i = j) := by
  exact compTree_eval_list B.instrs x i j

/-- The composition tree of an instruction list `l` has depth logarithmic in `|l|`:
`(compTree l i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 l.length + 1`.  Glue.

**Proof sketch.** Well-founded recursion on `l.length`, following `compTree`.  The leaves have
depth `≤ 1` (`depth_const`, `Instr.depth_wire_le`).  For `L = |l| ≥ 2`: (Step 1)
`⌈log₂ L⌉ = ⌈log₂ ⌈L/2⌉⌉ + 1` (`Nat.clog_of_two_le`); (Step 2) both halves have length
`≤ ⌈L/2⌉` (`List.length_take`, `List.length_drop`), so by the recursive calls and
`Nat.clog_mono_right` their wires have depth `≤ (⌈log₂ w⌉ + 2)·⌈log₂ ⌈L/2⌉⌉ + 1`; (Step 3)
`depth_wireComp_le` adds `⌈log₂ w⌉ + 2`. -/
private theorem depth_compTree_list_le :
    ∀ (l : List (Instr w n)) (i j : Fin w),
      (compTree l i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 l.length + 1
  | [], i, j => by
    rw [compTree_nil]
    split_ifs <;>
      (rw [← TreeCircuit.const_eq, TreeCircuit.depth_const]; exact Nat.le_add_left 1 _)
  | [ι], i, j => by
    rw [compTree_singleton]
    exact (Instr.depth_wire_le ι i j).trans (Nat.le_add_left 1 _)
  | ι₁ :: ι₂ :: l, i, j => by
    -- Step 1: `⌈log₂ L⌉ = ⌈log₂ ⌈L/2⌉⌉ + 1` for the length `L ≥ 2`.
    have hlen : 2 ≤ (ι₁ :: ι₂ :: l).length := by
      rw [List.length_cons, List.length_cons]
      omega
    have hc := Nat.clog_of_two_le (b := 2) (by norm_num) hlen
    -- Step 2: both halves have length at most `⌈L/2⌉`, so the induction hypothesis bounds them.
    have hT : ∀ i j, (compTree ((ι₁ :: ι₂ :: l).take ((ι₁ :: ι₂ :: l).length / 2)) i j).depth ≤
        (Nat.clog 2 w + 2) * Nat.clog 2 (((ι₁ :: ι₂ :: l).length + 2 - 1) / 2) + 1 := by
      intro i j
      refine (depth_compTree_list_le _ i j).trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.clog_mono_right 2 ?_)) 1)
      rw [List.length_take]
      omega
    have hD : ∀ i j, (compTree ((ι₁ :: ι₂ :: l).drop ((ι₁ :: ι₂ :: l).length / 2)) i j).depth ≤
        (Nat.clog 2 w + 2) * Nat.clog 2 (((ι₁ :: ι₂ :: l).length + 2 - 1) / 2) + 1 := by
      intro i j
      refine (depth_compTree_list_le _ i j).trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.clog_mono_right 2 ?_)) 1)
      rw [List.length_drop]
      omega
    -- Step 3: one composition circuit adds `⌈log₂ w⌉ + 2` levels.
    rw [compTree_cons_cons]
    refine (depth_wireComp_le hT hD i j).trans ?_
    rw [hc, Nat.mul_add_one]
    omega
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

/-- **C19.** The composition tree has depth `O(log l)`:
`(compTree B.instrs i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1`
[Bar89, Thm 2 proof, p004-b003].
Constant (fixed at the statement phase): the leaves have depth `≤ 1` (identity wires and
`Instr.wire`), and a list of length `l ≥ 2` splits into halves of lengths `⌊l/2⌋ ≤ ⌈l/2⌉` with
`⌈log₂ ⌈l/2⌉⌉ = ⌈log₂ l⌉ − 1`, each split adding `⌈log₂ w⌉ + 2` levels (C18).

**Proof sketch.** `length_eq` and the helper `depth_compTree_list_le`, by well-founded recursion on
the length `l` of the instruction list: `compTree_nil` (`depth_const`), `compTree_singleton` with
`Instr.depth_wire_le` give depth `≤ 1`; for `l ≥ 2`, `compTree_cons_cons` and `depth_wireComp_le`
with the recursive calls for both halves of length `≤ ⌈l/2⌉` (`List.length_take`,
`List.length_drop`), `Nat.clog_mono_right` and `Nat.clog_of_two_le`
(`⌈log₂ l⌉ = ⌈log₂ ⌈l/2⌉⌉ + 1`). -/
theorem depth_compTree_le (B : BranchingProgram w n) (i j : Fin w) :
    (compTree B.instrs i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1 := by
  rw [length_eq]
  exact depth_compTree_list_le B.instrs i j

/-- The composition tree of an instruction list `l` has fan-in 2:
`(compTree l i j).maxFanin ≤ 2`.  Glue. -/
private theorem maxFanin_compTree_list_le :
    ∀ (l : List (Instr w n)) (i j : Fin w), (compTree l i j).maxFanin ≤ 2
  | [], i, j => by
    rw [compTree_nil]
    split_ifs <;>
      (rw [← TreeCircuit.const_eq, TreeCircuit.maxFanin_const]; exact Nat.zero_le 2)
  | [ι], i, j => by
    rw [compTree_singleton]
    exact Instr.maxFanin_wire_le ι i j
  | ι₁ :: ι₂ :: l, i, j => by
    rw [compTree_cons_cons]
    exact maxFanin_wireComp_le
      (fun i j => maxFanin_compTree_list_le
        ((ι₁ :: ι₂ :: l).take ((ι₁ :: ι₂ :: l).length / 2)) i j)
      (fun i j => maxFanin_compTree_list_le
        ((ι₁ :: ι₂ :: l).drop ((ι₁ :: ι₂ :: l).length / 2)) i j) i j
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

/-- **C19.** The composition tree has fan-in at most 2: `(compTree B.instrs i j).maxFanin ≤ 2`.
Glue.

**Proof sketch.** The helper `maxFanin_compTree_list_le`, by well-founded recursion on the length
as for `compTree_eval`: the leaves by `compTree_nil` (`maxFanin_const`) and
`Instr.maxFanin_wire_le`; a composition circuit by the helper `maxFanin_wireComp_le`
(`wireComp_eq`, `TreeCircuit.maxFanin_balanced_le` and `maxFanin_and2_le` on the binary `∧`
nodes). -/
theorem maxFanin_compTree_le (B : BranchingProgram w n) (i j : Fin w) :
    (compTree B.instrs i j).maxFanin ≤ 2 := by
  exact maxFanin_compTree_list_le B.instrs i j

/-- **C20.** Barrington's Theorem 2 formula decides acceptance:
`(B.toFormula F).eval x = decide (B.yield x ∈ F)` [Bar89, Thm 2, p004-b003].

**Proof sketch.** `toFormula_eq`, `TreeCircuit.balanced_eval`, `eval_node_false_iff` (some `f` of
`F.toList`, `Finset.mem_toList`) and `eval_node_true_iff` (every `i` of `finRange w`); by
`compTree_eval` the conjunction for `f` holds iff `∀ i, B.yield x i = f i`, i.e.
`B.yield x = f` (`funext`). -/
theorem toFormula_eval (B : BranchingProgram w n) (F : Finset (Fin w → Fin w))
    (x : Fin n → Bool) : (B.toFormula F).eval x = decide (B.yield x ∈ F) := by
  rw [toFormula_eq, TreeCircuit.balanced_eval, Bool.eq_iff_iff, TreeCircuit.eval_node_false_iff,
    decide_eq_true_iff]
  constructor
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hc
    rw [TreeCircuit.balanced_eval, TreeCircuit.eval_node_true_iff] at hcx
    have hy : B.yield x = f := funext fun i => by
      have hi := hcx _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
      rwa [compTree_eval, decide_eq_true_iff] at hi
    rw [hy]
    exact Finset.mem_toList.1 hf
  · intro h
    refine ⟨_, List.mem_map.2 ⟨B.yield x, Finset.mem_toList.2 h, rfl⟩, ?_⟩
    rw [TreeCircuit.balanced_eval, TreeCircuit.eval_node_true_iff]
    intro c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    rw [compTree_eval, decide_eq_true_iff]

/-- **C21.** Depth `O(log l)` with a constant depending on `w`:
`(B.toFormula F).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + topDepth w`
[Bar89, Thm 2, p004-b003: "depth `O(log l)`, where the constant depends on `w`"].
Constant (fixed at the statement phase): `topDepth w = w·⌈log₂ w⌉ + ⌈log₂ w⌉ + 3`; r3's draft
`+ 4` is one more than needed.

**Proof sketch.** `toFormula_eq` and `TreeCircuit.depth_balanced_le` twice.  The inner `⋀_i` over
`w` wires of depth `≤ T = (⌈log₂ w⌉ + 2)·⌈log₂ l⌉ + 1` (`depth_compTree_le`) has depth
`≤ T + ⌈log₂ w⌉ + 1`; the outer `⋁_f` over `|F| ≤ w^w` terms (`Finset.length_toList`,
`Finset.card_le_univ`, `Fintype.card_fun`) adds `⌈log₂ |F|⌉ + 1 ≤ w·⌈log₂ w⌉ + 1`
(`Nat.clog_le_iff_le_pow` with `|F| ≤ w^w ≤ (2^⌈log₂ w⌉)^w`, `Fintype.card_fin`,
`Nat.le_pow_clog`, `Nat.pow_le_pow_left`, `pow_mul`); the members' depth bounds pass to the lists
by `maxDepth_le_of_forall`; `topDepth_eq` closes the arithmetic. -/
theorem depth_toFormula_le (B : BranchingProgram w n) (F : Finset (Fin w → Fin w)) :
    (B.toFormula F).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + topDepth w := by
  rw [toFormula_eq]
  refine (TreeCircuit.depth_balanced_le _ _).trans ?_
  rw [List.length_map, Finset.length_toList]
  -- Step 1: each conjunction `⋀_i` has depth `≤ T + ⌈log₂ w⌉ + 1`.
  have hin : TreeCircuit.maxDepth (F.toList.map fun f => TreeCircuit.balanced true
      ((List.finRange w).map fun i => compTree B.instrs i (f i))) ≤
      (Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1 + Nat.clog 2 w + 1 := by
    refine maxDepth_le_of_forall fun c hc => ?_
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hc
    refine (TreeCircuit.depth_balanced_le _ _).trans ?_
    rw [List.length_map, List.length_finRange]
    have hm : TreeCircuit.maxDepth ((List.finRange w).map fun i => compTree B.instrs i (f i)) ≤
        (Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1 := by
      refine maxDepth_le_of_forall fun c hc => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
      exact depth_compTree_le B i (f i)
    omega
  -- Step 2: `⌈log₂ |F|⌉ ≤ w·⌈log₂ w⌉`, since `|F| ≤ w^w ≤ (2^⌈log₂ w⌉)^w`.
  have hF : Nat.clog 2 F.card ≤ w * Nat.clog 2 w := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    calc F.card ≤ Fintype.card (Fin w → Fin w) := Finset.card_le_univ F
      _ = w ^ w := by rw [Fintype.card_fun, Fintype.card_fin]
      _ ≤ (2 ^ Nat.clog 2 w) ^ w := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) w) w
      _ = 2 ^ (w * Nat.clog 2 w) := by rw [← pow_mul, Nat.mul_comm]
  -- Step 3: the arithmetic of `topDepth`.
  rw [topDepth_eq]
  omega

/-- **C21.** Barrington's Theorem 2 formula has fan-in at most 2: `(B.toFormula F).maxFanin ≤ 2`
[Bar89, Thm 2, p004-b003: "a fan-in 2 circuit"].

**Proof sketch.** `toFormula_eq`, `TreeCircuit.maxFanin_balanced_le` twice, and
`maxFanin_compTree_le` for the leaves (`maxFaninL` of a mapped list, by `maxFaninL_le_of_forall`).
-/
theorem maxFanin_toFormula_le (B : BranchingProgram w n) (F : Finset (Fin w → Fin w)) :
    (B.toFormula F).maxFanin ≤ 2 := by
  rw [toFormula_eq]
  refine (TreeCircuit.maxFanin_balanced_le _ _).trans
    (max_le le_rfl (maxFaninL_le_of_forall fun c hc => ?_))
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hc
  refine (TreeCircuit.maxFanin_balanced_le _ _).trans
    (max_le le_rfl (maxFaninL_le_of_forall fun c hc => ?_))
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact maxFanin_compTree_le B i (f i)

end BranchingProgram

-- liveness control: reads `BranchingProgram.yield` through its body
example (B : BranchingProgram 3 2) (x : Fin 2 → Bool) : B.yield x = B.instrs.foldl (fun f ι => ι.eval x ∘ f) id :=
  rfl
