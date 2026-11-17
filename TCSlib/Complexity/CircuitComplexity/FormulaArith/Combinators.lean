/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi, TCSlib contributors
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.CircuitComplexity.TreeDAG

/-!
# Formula combinators: the balanced binary gate

The first rows of the circuit and formula gadget registry (`machine-library-design.md`, "Circuit
and formula gadgets"): combinators on `BoolCircuit.TreeCircuit` formulas that the formula
arithmetic of `FormulaArith/` is built from.  This file starts with the balanced binary tree of
gates, `BoolCircuit.TreeCircuit.balanced`, which computes an unbounded `∧`/`∨` gate with fan-in
two at logarithmic extra depth.  It was the private `combine` of `TreeNCAC.lean`, promoted
with its computation unchanged; its proofs carry the five Q2-approved Rule 10 repairs.
`BoolCircuit.TreeCircuit.toBinary` now calls it from there.

## Main definitions

* `BoolCircuit.TreeCircuit.balanced` — the balanced binary tree of `b`-gates over a child list.
* `BoolCircuit.TreeCircuit.neg` — the De Morgan negation (literals flip sign, gates flip
  kind), depth- and fan-in-preserving.
* `BoolCircuit.TreeCircuit.subst` — substitution of formulas for variables (a negative
  literal becomes the negated formula).  Its literal case, renaming the variables, is the
  existing `BoolCircuit.TreeCircuit.reidx` (`BooleanAnalysis/LMN/CircuitReindex.lean`).
* `BoolCircuit.TreeCircuit.const` — the constant formula `node b []`.
* `BoolCircuit.TreeCircuit.and2`, `or2`, `xor2`, `xor3`, `maj3` — the fan-in-2 gadgets, of
  depth `+1`, `+1`, `+2`, `+4`, `+3` over their arguments.

## Main results

* `BoolCircuit.TreeCircuit.balanced_eval` — it computes the unbounded gate.
* `BoolCircuit.TreeCircuit.maxFanin_balanced_le`, `depth_balanced_le`, `size_balanced_le` —
  fan-in two, `⌈log₂ |cs|⌉ + 1` extra depth, `|cs| + 1` extra size.
* `BoolCircuit.TreeCircuit.balanced_nil`, `balanced_singleton` — the readers on short lists.
* `BoolCircuit.TreeCircuit.const_eval` — the constant formula evaluates to its constant (F3);
  proved from `BoolCircuit.eval_node_nil` (an empty gate is a constant), which moved here from
  `Hierarchy.lean`.
* `BoolCircuit.TreeCircuit.neg_eval`, `depth_neg`, `maxFanin_neg` — negation (F1; targets).
* `BoolCircuit.TreeCircuit.subst_eval`, `depth_subst_le`, `maxFanin_subst_le` — substitution
  (F2; targets).
* `BoolCircuit.TreeCircuit.xor3_eval`, `maj3_eval`, the other value lemmas of the fan-in-2
  gadgets, and the depth and fan-in lemmas of every gadget (F3; targets).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ### Simulating an unbounded gate by a balanced binary tree -/

/-- Pair adjacent children under a gate of type `b`, halving the list. -/
private def pairUp (b : Bool) : List (TreeCircuit n) → List (TreeCircuit n)
  | [] => []
  | [c] => [c]
  | c₁ :: c₂ :: cs => TreeCircuit.node b [c₁, c₂] :: pairUp b cs

/-- Pairing halves the list, rounding up. -/
private theorem length_pairUp (b : Bool) :
    ∀ cs : List (TreeCircuit n), (pairUp b cs).length = (cs.length + 1) / 2
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | _ :: _ :: cs => by
      have := length_pairUp b cs
      simp only [pairUp, List.length_cons] at *
      omega

/-- Pairing preserves the value of the surrounding gate. -/
private theorem eval_node_pairUp (b : Bool) (x : Fin n → Bool) :
    ∀ cs : List (TreeCircuit n),
      (TreeCircuit.node b (pairUp b cs)).eval x = (TreeCircuit.node b cs).eval x
  | [] => rfl
  | [_] => by cases b <;> simp [pairUp, TreeCircuit.eval_node_true, TreeCircuit.eval_node_false]
  | c₁ :: c₂ :: cs => by
      have := eval_node_pairUp b x cs
      cases b <;>
        simp only [pairUp, TreeCircuit.eval_node_true, TreeCircuit.eval_node_false,
          List.all_cons, List.all_nil, List.any_cons, List.any_nil] at * <;>
        simp [this, Bool.and_assoc, Bool.or_assoc]

/-- Pairing adds at most one to the depth. -/
private theorem maxDepth_pairUp (b : Bool) :
    ∀ cs : List (TreeCircuit n), TreeCircuit.maxDepth (pairUp b cs) ≤ 1 + TreeCircuit.maxDepth cs
  | [] => by simp [pairUp, TreeCircuit.maxDepth_nil]
  | [c] => by simp [pairUp]
  | c₁ :: c₂ :: cs => by
      have ih := maxDepth_pairUp b cs
      have h1 : (TreeCircuit.node b [c₁, c₂]).depth
          = 1 + max c₁.depth (max c₂.depth 0) := by
        rw [TreeCircuit.depth_node, TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_cons,
          TreeCircuit.maxDepth_nil]
      simp only [pairUp, TreeCircuit.maxDepth_cons, h1]
      omega

/-- Pairing does not increase the total size plus length. -/
private theorem sumSize_pairUp (b : Bool) :
    ∀ cs : List (TreeCircuit n),
      TreeCircuit.sumSize (pairUp b cs) + (pairUp b cs).length ≤
        TreeCircuit.sumSize cs + cs.length
  | [] => by rw [pairUp, TreeCircuit.sumSize_nil, List.length_nil]
  | [_] => le_refl _
  | c₁ :: c₂ :: cs => by
      have ih := sumSize_pairUp b cs
      have h1 : (TreeCircuit.node b [c₁, c₂]).size = 1 + (c₁.size + (c₂.size + 0)) := by
        rw [TreeCircuit.size_node, TreeCircuit.sumSize_cons, TreeCircuit.sumSize_cons,
          TreeCircuit.sumSize_nil]
      simp only [pairUp, TreeCircuit.sumSize_cons, h1, List.length_cons]
      omega

/-- Pairing introduces only fan-in-2 gates. -/
private theorem maxFaninL_pairUp (b : Bool) :
    ∀ cs : List (TreeCircuit n),
      TreeCircuit.maxFaninL (pairUp b cs) ≤ max 2 (TreeCircuit.maxFaninL cs)
  | [] => by rw [pairUp, TreeCircuit.maxFaninL_nil]; exact Nat.zero_le _
  | [c] => by simp [pairUp, TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_nil]
  | c₁ :: c₂ :: cs => by
      have ih := maxFaninL_pairUp b cs
      have h1 : (TreeCircuit.node b [c₁, c₂]).maxFanin
          = max 2 (max c₁.maxFanin (max c₂.maxFanin 0)) := by
        rw [TreeCircuit.maxFanin_node, TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_cons,
          TreeCircuit.maxFaninL_nil]
        norm_num
      simp only [pairUp, TreeCircuit.maxFaninL_cons, h1]
      omega

/-- Repeatedly pair a child list, `k` rounds at most, into a single circuit. -/
private def combineFuel (b : Bool) : ℕ → List (TreeCircuit n) → TreeCircuit n
  | 0, cs => TreeCircuit.node b cs
  | _ + 1, [] => TreeCircuit.node b []
  | _ + 1, [c] => c
  | k + 1, c₁ :: c₂ :: cs => combineFuel b k (pairUp b (c₁ :: c₂ :: cs))

/-- The balanced binary tree of `b`-gates over the child list `cs`: the children are paired
under fan-in-2 `b`-gates round by round (at most `|cs|` rounds) until one circuit is left,
`balanced b cs = combineFuel b |cs| cs`.  It computes the unbounded gate
`TreeCircuit.node b cs` (`TreeCircuit.balanced_eval`); `balanced b [] = node b []` and
`balanced b [c] = c`.  The former private `TreeNCAC.combine`, promoted for the formula
arithmetic layer; glue behind [AB09, p. 118]'s fan-in reduction (`TreeCircuit.toBinary`). -/
def TreeCircuit.balanced (b : Bool) (cs : List (TreeCircuit n)) : TreeCircuit n :=
  combineFuel b cs.length cs

/-- Combining computes the same value as the unbounded gate. -/
private theorem combineFuel_eval (b : Bool) (x : Fin n → Bool) :
    ∀ (k : ℕ) (cs : List (TreeCircuit n)),
      (combineFuel b k cs).eval x = (TreeCircuit.node b cs).eval x
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [c] => by
      cases b <;> simp [combineFuel, TreeCircuit.eval_node_true, TreeCircuit.eval_node_false]
  | k + 1, c₁ :: c₂ :: cs => by
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).eval x = _
      rw [combineFuel_eval b x k, eval_node_pairUp]

/-- Combining produces only fan-in-2 gates, given enough rounds. -/
private theorem combineFuel_maxFanin (b : Bool) :
    ∀ (k : ℕ) (cs : List (TreeCircuit n)), cs.length ≤ k →
      (combineFuel b k cs).maxFanin ≤ max 2 (TreeCircuit.maxFaninL cs)
  | 0, [], _ => by simp [combineFuel, TreeCircuit.maxFanin_node, TreeCircuit.maxFaninL_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, TreeCircuit.maxFanin_node, TreeCircuit.maxFaninL_nil]
  | _ + 1, [c], _ => by
      show c.maxFanin ≤ _
      rw [TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_nil]
      omega
  | k + 1, c₁ :: c₂ :: cs, h => by
      have hp := length_pairUp b (c₁ :: c₂ :: cs)
      have hlen : (pairUp b (c₁ :: c₂ :: cs)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := combineFuel_maxFanin b k _ hlen
      have h2 := maxFaninL_pairUp b (c₁ :: c₂ :: cs)
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).maxFanin ≤ _
      omega

/-- Combining `m` children costs `⌈log₂ m⌉` extra levels of depth.

**Proof sketch.** Induction on the fuel.  With no children, or one child, the bound is
immediate.  With at least two children, one round of pairing halves the list (to
`⌈m / 2⌉` entries) and raises the maximum child depth by at most one, while
`⌈log₂ m⌉ = ⌈log₂ ⌈m / 2⌉⌉ + 1` for `m ≥ 2`; the induction hypothesis on the paired list
then gives the bound. -/
private theorem combineFuel_depth (b : Bool) :
    ∀ (k : ℕ) (cs : List (TreeCircuit n)), cs.length ≤ k →
      (combineFuel b k cs).depth ≤ TreeCircuit.maxDepth cs + Nat.clog 2 cs.length + 1
  | 0, [], _ => by simp [combineFuel, TreeCircuit.depth_node, TreeCircuit.maxDepth_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, TreeCircuit.depth_node, TreeCircuit.maxDepth_nil]
  | _ + 1, [c], _ => by
      show c.depth ≤ _
      rw [TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_nil]
      simp
  | k + 1, c₁ :: c₂ :: cs, h => by
      have hp := length_pairUp b (c₁ :: c₂ :: cs)
      have hlen : (pairUp b (c₁ :: c₂ :: cs)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := combineFuel_depth b k _ hlen
      have h2 := maxDepth_pairUp b (c₁ :: c₂ :: cs)
      have hclog : Nat.clog 2 (c₁ :: c₂ :: cs).length
          = Nat.clog 2 ((pairUp b (c₁ :: c₂ :: cs)).length) + 1 := by
        rw [hp]
        have := Nat.clog_of_two_le (b := 2) (n := (c₁ :: c₂ :: cs).length)
          (by norm_num) (by simp)
        simpa using this
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).depth ≤ _
      omega

/-- Combining `m` children costs at most `m` extra gates. -/
private theorem combineFuel_size (b : Bool) :
    ∀ (k : ℕ) (cs : List (TreeCircuit n)),
      (combineFuel b k cs).size ≤ TreeCircuit.sumSize cs + cs.length + 1
  | 0, cs => by show (TreeCircuit.node b cs).size ≤ _; rw [TreeCircuit.size_node]; omega
  | _ + 1, [] => by simp [combineFuel, TreeCircuit.size_node, TreeCircuit.sumSize_nil]
  | _ + 1, [c] => by show c.size ≤ _; rw [TreeCircuit.sumSize_cons, TreeCircuit.sumSize_nil]; omega
  | k + 1, c₁ :: c₂ :: cs => by
      have ih := combineFuel_size b k (pairUp b (c₁ :: c₂ :: cs))
      have h2 := sumSize_pairUp b (c₁ :: c₂ :: cs)
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).size ≤ _
      omega

/-- The balanced tree computes the unbounded gate:
`(TreeCircuit.balanced b cs).eval x = (TreeCircuit.node b cs).eval x`. -/
theorem TreeCircuit.balanced_eval (b : Bool) (cs : List (TreeCircuit n)) (x : Fin n → Bool) :
    (TreeCircuit.balanced b cs).eval x = (TreeCircuit.node b cs).eval x :=
  combineFuel_eval b x _ cs

/-- The balanced tree has fan-in 2, unless a child already had more:
`(TreeCircuit.balanced b cs).maxFanin ≤ max 2 (TreeCircuit.maxFaninL cs)`. -/
theorem TreeCircuit.maxFanin_balanced_le (b : Bool) (cs : List (TreeCircuit n)) :
    (TreeCircuit.balanced b cs).maxFanin ≤ max 2 (TreeCircuit.maxFaninL cs) :=
  combineFuel_maxFanin b _ cs (le_refl _)

/-- The balanced tree adds at most `⌈log₂ |cs|⌉ + 1` to the children's depth:
`(TreeCircuit.balanced b cs).depth ≤ TreeCircuit.maxDepth cs + Nat.clog 2 cs.length + 1`. -/
theorem TreeCircuit.depth_balanced_le (b : Bool) (cs : List (TreeCircuit n)) :
    (TreeCircuit.balanced b cs).depth ≤ TreeCircuit.maxDepth cs + Nat.clog 2 cs.length + 1 :=
  combineFuel_depth b _ cs (le_refl _)

/-- The balanced tree adds at most `|cs| + 1` to the children's total size:
`(TreeCircuit.balanced b cs).size ≤ TreeCircuit.sumSize cs + cs.length + 1`. -/
theorem TreeCircuit.size_balanced_le (b : Bool) (cs : List (TreeCircuit n)) :
    (TreeCircuit.balanced b cs).size ≤ TreeCircuit.sumSize cs + cs.length + 1 :=
  combineFuel_size b _ cs

/-- The balanced tree over no children is the empty gate: `TreeCircuit.balanced b [] =
TreeCircuit.node b []`. -/
theorem TreeCircuit.balanced_nil (b : Bool) :
    TreeCircuit.balanced b ([] : List (TreeCircuit n)) = TreeCircuit.node b [] := rfl

/-- The balanced tree over one child is that child: `TreeCircuit.balanced b [c] = c`. -/
theorem TreeCircuit.balanced_singleton (b : Bool) (c : TreeCircuit n) :
    TreeCircuit.balanced b [c] = c := rfl

/-! ### De Morgan negation and substitution (F1–F2) -/

mutual

/-- The De Morgan negation of a formula: every literal flips its sign and every gate flips its
kind, `(lit ⟨i, s⟩).neg = lit ⟨i, !s⟩` and `(node b cs).neg = node (!b) (cs.map neg)`, so
that `c.neg` computes `!c.eval x` with the same shape, depth and fan-in
(`TreeCircuit.neg_eval`, `depth_neg`, `maxFanin_neg`).  Structural recursion over the nested
child list, through the private list helper `negList`.  Glue. -/
def TreeCircuit.neg : TreeCircuit n → TreeCircuit n
  | .lit l => .lit ⟨l.idx, !l.sign⟩
  | .node b cs => .node (!b) (negList cs)

/-- `TreeCircuit.neg` on every member of a child list: `negList cs = cs.map neg`. -/
private def negList : List (TreeCircuit n) → List (TreeCircuit n)
  | [] => []
  | c :: cs => c.neg :: negList cs

end

/-- The negation of a literal flips its sign:
`(TreeCircuit.lit l).neg = TreeCircuit.lit ⟨l.idx, !l.sign⟩`. -/
theorem TreeCircuit.neg_lit (l : Lit n) :
    (TreeCircuit.lit l).neg = TreeCircuit.lit ⟨l.idx, !l.sign⟩ := rfl

/-- The list helper of `neg` is `List.map`: `negList cs = cs.map TreeCircuit.neg`. -/
private theorem negList_eq_map : ∀ cs : List (TreeCircuit n), negList cs = cs.map TreeCircuit.neg
  | [] => rfl
  | c :: cs => congrArg (c.neg :: ·) (negList_eq_map cs)

/-- The negation of a gate flips its kind and negates every child:
`(TreeCircuit.node b cs).neg = TreeCircuit.node (!b) (cs.map TreeCircuit.neg)`. -/
theorem TreeCircuit.neg_node (b : Bool) (cs : List (TreeCircuit n)) :
    (TreeCircuit.node b cs).neg = TreeCircuit.node (!b) (cs.map TreeCircuit.neg) :=
  congrArg (TreeCircuit.node (!b)) (negList_eq_map cs)

/-- **F1, value.** The De Morgan negation computes the negation:
`c.neg.eval x = !c.eval x`.  Glue (r3 §H5.7, F1).

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`).  A literal: `neg_lit`, then
`eval_lit` and the value of a literal (`Lit.eval`, whose reader is missing; see the census)
with the sign flipped.  A gate `node b cs`: `neg_node`; for `b = true` the negated gate is an
`∨`-gate, so `eval_node_false` gives `(cs.map neg).any (·.eval x)`, which by the induction
hypothesis is `cs.any (! ·.eval x) = !(cs.all (·.eval x))`, that is `!` of `eval_node_true`;
`b = false` is symmetric. -/
theorem TreeCircuit.neg_eval (c : TreeCircuit n) (x : Fin n → Bool) :
    c.neg.eval x = !c.eval x := by
  induction c using TreeCircuit.ind with
  | hlit l =>
    obtain ⟨i, s⟩ := l
    rw [TreeCircuit.neg_lit, TreeCircuit.eval_lit, TreeCircuit.eval_lit, Lit.eval_eq, Lit.eval_eq]
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.not_not, Bool.false_eq_true,
      ↓reduceIte]
  | hnode b cs ih =>
    rw [TreeCircuit.neg_node]
    cases b
    · rw [Bool.not_false, TreeCircuit.eval_node_true, TreeCircuit.eval_node_false, List.all_map,
        all_congr_mem (p := (fun c : TreeCircuit n => c.eval x) ∘ TreeCircuit.neg)
          (q := fun c => !c.eval x) fun c hc => ih c hc, List.not_any_eq_all_not]
    · rw [Bool.not_true, TreeCircuit.eval_node_false, TreeCircuit.eval_node_true, List.any_map,
        any_congr_mem (p := (fun c : TreeCircuit n => c.eval x) ∘ TreeCircuit.neg)
          (q := fun c => !c.eval x) fun c hc => ih c hc, List.not_all_eq_any_not]

/-- **F1, depth.** De Morgan negation preserves the depth: `c.neg.depth = c.depth`.  Glue.

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`).  A literal stays a literal (depth `0`
on both sides; the reader `depth_lit` is missing, see the census).  A gate: `neg_node` and
`depth_node` reduce the claim to `maxDepth (cs.map neg) = maxDepth cs`, an induction on the
list with `maxDepth_nil`/`maxDepth_cons` and the induction hypothesis on each child. -/
theorem TreeCircuit.depth_neg (c : TreeCircuit n) : c.neg.depth = c.depth := by
  induction c using TreeCircuit.ind with
  | hlit l => rw [TreeCircuit.neg_lit, TreeCircuit.depth_lit, TreeCircuit.depth_lit]
  | hnode b cs ih =>
    rw [TreeCircuit.neg_node, TreeCircuit.depth_node, TreeCircuit.depth_node]
    -- the list maximum is unchanged, child by child
    induction cs with
    | nil => rw [List.map_nil]
    | cons c cs ihl =>
      rw [List.map_cons, TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_cons,
        ih c (List.mem_cons_self ..)]
      have := ihl fun d hd => ih d (List.mem_cons_of_mem _ hd)
      omega

/-- **F1, fan-in.** De Morgan negation preserves the fan-in: `c.neg.maxFanin = c.maxFanin`.
Glue.

**Proof sketch.** As for `depth_neg`: induction on `c`; a gate keeps its arity
(`List.length_map`), and `maxFanin_node` with `maxFaninL_nil`/`maxFaninL_cons` and the
induction hypothesis gives `maxFaninL (cs.map neg) = maxFaninL cs`. -/
theorem TreeCircuit.maxFanin_neg (c : TreeCircuit n) : c.neg.maxFanin = c.maxFanin := by
  induction c using TreeCircuit.ind with
  | hlit l => rw [TreeCircuit.neg_lit, TreeCircuit.maxFanin_lit, TreeCircuit.maxFanin_lit]
  | hnode b cs ih =>
    rw [TreeCircuit.neg_node, TreeCircuit.maxFanin_node, TreeCircuit.maxFanin_node, List.length_map]
    -- the children's maximum fan-in is unchanged, child by child
    induction cs with
    | nil => rw [List.map_nil]
    | cons c cs ihl =>
      rw [List.map_cons, TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_cons,
        ih c (List.mem_cons_self ..)]
      have := ihl fun d hd => ih d (List.mem_cons_of_mem _ hd)
      simp only [List.length_cons] at this ⊢
      omega

mutual

/-- Substitution of formulas for variables: `c.subst f` replaces every positive literal
`x_i` of `c` by `f i` and every negative literal `¬x_i` by `(f i).neg`, keeping the gates,
`(lit l).subst f = if l.sign then f l.idx else (f l.idx).neg` and
`(node b cs).subst f = node b (cs.map (·.subst f))`.  It computes `c` on the values of the
`f i` (`TreeCircuit.subst_eval`).  Structural recursion over the nested child list, through
the private list helper `substList`.  Glue. -/
def TreeCircuit.subst {m : ℕ} : TreeCircuit n → (Fin n → TreeCircuit m) → TreeCircuit m
  | .lit l, f => if l.sign then f l.idx else (f l.idx).neg
  | .node b cs, f => .node b (substList cs f)

/-- `TreeCircuit.subst` on every member of a child list:
`substList cs f = cs.map (·.subst f)`. -/
private def substList {m : ℕ} :
    List (TreeCircuit n) → (Fin n → TreeCircuit m) → List (TreeCircuit m)
  | [], _ => []
  | c :: cs, f => c.subst f :: substList cs f

end

/-- Substitution into a literal: the positive literal `x_i` becomes `f i` and the negative
literal `¬x_i` becomes `(f i).neg`,
`(TreeCircuit.lit l).subst f = if l.sign then f l.idx else (f l.idx).neg`. -/
theorem TreeCircuit.subst_lit {m : ℕ} (l : Lit n) (f : Fin n → TreeCircuit m) :
    (TreeCircuit.lit l).subst f = if l.sign then f l.idx else (f l.idx).neg := rfl

/-- The list helper of `subst` is `List.map`: `substList cs f = cs.map (·.subst f)`. -/
private theorem substList_eq_map {m : ℕ} (f : Fin n → TreeCircuit m) :
    ∀ cs : List (TreeCircuit n), substList cs f = cs.map fun c => c.subst f
  | [] => rfl
  | c :: cs => congrArg (c.subst f :: ·) (substList_eq_map f cs)

/-- Substitution into a gate substitutes into every child:
`(TreeCircuit.node b cs).subst f = TreeCircuit.node b (cs.map fun c => c.subst f)`. -/
theorem TreeCircuit.subst_node {m : ℕ} (b : Bool) (cs : List (TreeCircuit n))
    (f : Fin n → TreeCircuit m) :
    (TreeCircuit.node b cs).subst f = TreeCircuit.node b (cs.map fun c => c.subst f) :=
  congrArg (TreeCircuit.node b) (substList_eq_map f cs)

/-- **F2, value.** Substitution computes the formula on the substituted values:
`(c.subst f).eval x = c.eval fun i => (f i).eval x`.  Glue (r3 §H5.7, F2).

**Proof sketch.** Induction on `c` (`TreeCircuit.ind`).  A positive literal: `subst_lit`, and
both sides are `(f i).eval x` (`eval_lit` and the literal's value).  A negative literal: the
left side is `(f i).neg.eval x = !(f i).eval x` by `neg_eval`, which is the value of `¬x_i`
under `fun i => (f i).eval x`.  A gate: `subst_node`, then `eval_node_true`/`eval_node_false`
on both sides, `List.all_map`/`List.any_map` and the induction hypothesis on each child. -/
theorem TreeCircuit.subst_eval {m : ℕ} (c : TreeCircuit n) (f : Fin n → TreeCircuit m)
    (x : Fin m → Bool) : (c.subst f).eval x = c.eval fun i => (f i).eval x := by
  induction c using TreeCircuit.ind with
  | hlit l =>
    obtain ⟨i, s⟩ := l
    rw [TreeCircuit.subst_lit, TreeCircuit.eval_lit, Lit.eval_eq]
    cases s
    · exact TreeCircuit.neg_eval (f i) x
    · rfl
  | hnode b cs ih =>
    rw [TreeCircuit.subst_node]
    cases b
    · rw [TreeCircuit.eval_node_false, TreeCircuit.eval_node_false, List.any_map]
      exact any_congr_mem fun c hc => ih c hc
    · rw [TreeCircuit.eval_node_true, TreeCircuit.eval_node_true, List.all_map]
      exact all_congr_mem fun c hc => ih c hc

/-- **F2, depth.** Substitution adds at most the depth of the deepest substituted formula:
`(c.subst f).depth ≤ c.depth + Finset.univ.sup fun i => (f i).depth`.  Glue (r3 §H5.7, F2).

*Deviation from r3's sketch:* r3 writes `⨆ i, (f i).depth`; `SupSet ℕ` is not in this file's
(frozen) import closure, so the supremum over the finite index type is the equal
`Finset.univ.sup`.

**Proof sketch.** Induction on `c`, with `D = Finset.univ.sup fun i => (f i).depth`.  A
literal: the result is `f i` or `(f i).neg`, of depth `(f i).depth ≤ D`
(`depth_neg`, `Finset.le_sup`), and `c.depth = 0`.  A gate: `subst_node` and `depth_node` give
`1 + maxDepth (cs.map (·.subst f))`; each child is bounded by `child.depth + D` (induction
hypothesis) `≤ maxDepth cs + D` (`depth_le_maxDepth`), so the list maximum is too
(`maxDepth_nil`/`maxDepth_cons`), and `depth_node` on `c` closes it. -/
theorem TreeCircuit.depth_subst_le {m : ℕ} (c : TreeCircuit n) (f : Fin n → TreeCircuit m) :
    (c.subst f).depth ≤ c.depth + Finset.univ.sup fun i => (f i).depth := by
  induction c using TreeCircuit.ind with
  | hlit l =>
    have hD : (f l.idx).depth ≤ Finset.univ.sup fun i => (f i).depth :=
      Finset.le_sup (f := fun i => (f i).depth) (Finset.mem_univ _)
    rw [TreeCircuit.subst_lit, TreeCircuit.depth_lit, Nat.zero_add]
    split
    · exact hD
    · rw [TreeCircuit.depth_neg]; exact hD
  | hnode b cs ih =>
    rw [TreeCircuit.subst_node, TreeCircuit.depth_node, TreeCircuit.depth_node]
    -- each substituted child is at most `D` deeper than the deepest old child
    suffices h : TreeCircuit.maxDepth (cs.map fun c => c.subst f) ≤
        TreeCircuit.maxDepth cs + Finset.univ.sup fun i => (f i).depth by omega
    induction cs with
    | nil => rw [List.map_nil, TreeCircuit.maxDepth_nil]; exact Nat.zero_le _
    | cons c cs ihl =>
      rw [List.map_cons, TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_cons]
      have h1 := ih c (List.mem_cons_self ..)
      have h2 := ihl fun d hd => ih d (List.mem_cons_of_mem _ hd)
      omega

/-- **F2, fan-in.** Substitution has the fan-in of the formula or of a substituted formula:
`(c.subst f).maxFanin ≤ max c.maxFanin (Finset.univ.sup fun i => (f i).maxFanin)`.  Glue
(r3 §H5.7, F2; r3 names the lemma without a formula, and `⨆` is written `Finset.univ.sup` as
in `depth_subst_le`).

**Proof sketch.** Induction on `c` as in `depth_subst_le`.  A literal becomes `f i` or
`(f i).neg`, of fan-in `(f i).maxFanin` (`maxFanin_neg`, `Finset.le_sup`).  A gate keeps its
arity (`subst_node`, `List.length_map`), and `maxFanin_node`, `maxFaninL_cons` and the
induction hypothesis bound the children. -/
theorem TreeCircuit.maxFanin_subst_le {m : ℕ} (c : TreeCircuit n) (f : Fin n → TreeCircuit m) :
    (c.subst f).maxFanin ≤ max c.maxFanin (Finset.univ.sup fun i => (f i).maxFanin) := by
  induction c using TreeCircuit.ind with
  | hlit l =>
    have hM : (f l.idx).maxFanin ≤ Finset.univ.sup fun i => (f i).maxFanin :=
      Finset.le_sup (f := fun i => (f i).maxFanin) (Finset.mem_univ _)
    rw [TreeCircuit.subst_lit, TreeCircuit.maxFanin_lit]
    split
    · exact le_max_of_le_right hM
    · rw [TreeCircuit.maxFanin_neg]; exact le_max_of_le_right hM
  | hnode b cs ih =>
    rw [TreeCircuit.subst_node, TreeCircuit.maxFanin_node, TreeCircuit.maxFanin_node,
      List.length_map]
    -- each substituted child has fan-in at most that of an old child or of some `f i`
    suffices h : TreeCircuit.maxFaninL (cs.map fun c => c.subst f) ≤
        max (TreeCircuit.maxFaninL cs) (Finset.univ.sup fun i => (f i).maxFanin) by omega
    induction cs with
    | nil => rw [List.map_nil, TreeCircuit.maxFaninL_nil]; exact Nat.zero_le _
    | cons c cs ihl =>
      rw [List.map_cons, TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_cons]
      have h1 := ih c (List.mem_cons_self ..)
      have h2 := ihl fun d hd => ih d (List.mem_cons_of_mem _ hd)
      omega

/-! ### Constants and the fan-in-2 gadgets (F3) -/

/-- An empty gate is a constant: the empty `AND` is `true`, the empty `OR` is `false`. -/
theorem eval_node_nil (b : Bool) (x : Fin n → Bool) :
    (TreeCircuit.node b ([] : List (TreeCircuit n))).eval x = b := by
  cases b <;> simp [TreeCircuit.eval_node_true, TreeCircuit.eval_node_false]

/-- The constant formula with value `b`: the empty gate, `TreeCircuit.const b = node b []`
(an empty `∧` is `true`, an empty `∨` is `false`).  Depth `1`, fan-in `0`.  Glue. -/
def TreeCircuit.const (b : Bool) : TreeCircuit n :=
  .node b []

/-- The constant formula is the empty gate:
`(TreeCircuit.const b : TreeCircuit n) = TreeCircuit.node b []`. -/
theorem TreeCircuit.const_eq (b : Bool) :
    (TreeCircuit.const b : TreeCircuit n) = TreeCircuit.node b [] := rfl

/-- **F3, constant: value.** The constant formula evaluates to its constant:
`(TreeCircuit.const b).eval x = b`.  This is `BoolCircuit.eval_node_nil` read through
`const_eq`. -/
theorem TreeCircuit.const_eval (b : Bool) (x : Fin n → Bool) :
    (TreeCircuit.const b : TreeCircuit n).eval x = b := by
  rw [TreeCircuit.const_eq]; exact eval_node_nil b x

/-- **F3, constant: depth.** The constant formula has depth one:
`(TreeCircuit.const b : TreeCircuit n).depth = 1`.  Glue.

**Proof sketch.** `const_eq`, `depth_node` and `maxDepth_nil`. -/
theorem TreeCircuit.depth_const (b : Bool) : (TreeCircuit.const b : TreeCircuit n).depth = 1 := by
  rw [TreeCircuit.const_eq, TreeCircuit.depth_node, TreeCircuit.maxDepth_nil]

/-- **F3, constant: fan-in.** The constant formula has fan-in zero:
`(TreeCircuit.const b : TreeCircuit n).maxFanin = 0`.  Glue.

**Proof sketch.** `const_eq`, `maxFanin_node`, `List.length_nil` and `maxFaninL_nil`. -/
theorem TreeCircuit.maxFanin_const (b : Bool) :
    (TreeCircuit.const b : TreeCircuit n).maxFanin = 0 := by
  rw [TreeCircuit.const_eq, TreeCircuit.maxFanin_node, List.length_nil, TreeCircuit.maxFaninL_nil,
    Nat.max_self]

/-- The binary conjunction `TreeCircuit.and2 a b = node true [a, b]`.  Glue. -/
def TreeCircuit.and2 (a b : TreeCircuit n) : TreeCircuit n :=
  .node true [a, b]

/-- The binary conjunction is a two-child `∧`-gate:
`TreeCircuit.and2 a b = TreeCircuit.node true [a, b]`. -/
theorem TreeCircuit.and2_eq (a b : TreeCircuit n) :
    TreeCircuit.and2 a b = TreeCircuit.node true [a, b] := rfl

/-- The binary disjunction `TreeCircuit.or2 a b = node false [a, b]`.  Glue. -/
def TreeCircuit.or2 (a b : TreeCircuit n) : TreeCircuit n :=
  .node false [a, b]

/-- The binary disjunction is a two-child `∨`-gate:
`TreeCircuit.or2 a b = TreeCircuit.node false [a, b]`. -/
theorem TreeCircuit.or2_eq (a b : TreeCircuit n) :
    TreeCircuit.or2 a b = TreeCircuit.node false [a, b] := rfl

/-- The binary exclusive or `TreeCircuit.xor2 a b = or2 (and2 a b.neg) (and2 a.neg b)`, that
is `(a ∧ ¬b) ∨ (¬a ∧ b)` with the negations by De Morgan (`neg`).  Two levels above its
arguments.  Glue. -/
def TreeCircuit.xor2 (a b : TreeCircuit n) : TreeCircuit n :=
  TreeCircuit.or2 (TreeCircuit.and2 a b.neg) (TreeCircuit.and2 a.neg b)

/-- The exclusive or as a formula:
`TreeCircuit.xor2 a b = TreeCircuit.or2 (TreeCircuit.and2 a b.neg) (TreeCircuit.and2 a.neg b)`.
-/
theorem TreeCircuit.xor2_eq (a b : TreeCircuit n) :
    TreeCircuit.xor2 a b = TreeCircuit.or2 (TreeCircuit.and2 a b.neg) (TreeCircuit.and2 a.neg b) :=
  rfl

/-- The three-input exclusive or (the full adder's sum bit)
`TreeCircuit.xor3 a b c = xor2 (xor2 a b) c`.  Four levels above its arguments.  Glue. -/
def TreeCircuit.xor3 (a b c : TreeCircuit n) : TreeCircuit n :=
  TreeCircuit.xor2 (TreeCircuit.xor2 a b) c

/-- The three-input exclusive or as nested binary ones:
`TreeCircuit.xor3 a b c = TreeCircuit.xor2 (TreeCircuit.xor2 a b) c`. -/
theorem TreeCircuit.xor3_eq (a b c : TreeCircuit n) :
    TreeCircuit.xor3 a b c = TreeCircuit.xor2 (TreeCircuit.xor2 a b) c := rfl

/-- The three-input majority (the full adder's carry bit)
`TreeCircuit.maj3 a b c = or2 (and2 a b) (and2 c (or2 a b))`, that is
`(a ∧ b) ∨ (c ∧ (a ∨ b))`.  Three levels above its arguments.  Glue. -/
def TreeCircuit.maj3 (a b c : TreeCircuit n) : TreeCircuit n :=
  TreeCircuit.or2 (TreeCircuit.and2 a b) (TreeCircuit.and2 c (TreeCircuit.or2 a b))

/-- The majority as a formula: `TreeCircuit.maj3 a b c =
TreeCircuit.or2 (TreeCircuit.and2 a b) (TreeCircuit.and2 c (TreeCircuit.or2 a b))`. -/
theorem TreeCircuit.maj3_eq (a b c : TreeCircuit n) :
    TreeCircuit.maj3 a b c =
      TreeCircuit.or2 (TreeCircuit.and2 a b) (TreeCircuit.and2 c (TreeCircuit.or2 a b)) := rfl

/-- **F3, `and2`: value.** `(TreeCircuit.and2 a b).eval x = (a.eval x && b.eval x)`.  Glue.

**Proof sketch.** `and2_eq`, `eval_node_true`, and `List.all_cons`/`List.all_nil`. -/
theorem TreeCircuit.and2_eval (a b : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.and2 a b).eval x = (a.eval x && b.eval x) := by
  rw [TreeCircuit.and2_eq, TreeCircuit.eval_node_true, List.all_cons, List.all_cons, List.all_nil,
    Bool.and_true]

/-- **F3, `and2`: depth `+1`.** `(TreeCircuit.and2 a b).depth ≤ max a.depth b.depth + 1`.
Glue.

**Proof sketch.** `and2_eq`, `depth_node`, `maxDepth_cons` twice and `maxDepth_nil`; then
`omega` (it is an equality). -/
theorem TreeCircuit.depth_and2_le (a b : TreeCircuit n) :
    (TreeCircuit.and2 a b).depth ≤ max a.depth b.depth + 1 := by
  rw [TreeCircuit.and2_eq, TreeCircuit.depth_node, TreeCircuit.maxDepth_cons,
    TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_nil]
  omega

/-- **F3, `and2`: fan-in two.**
`(TreeCircuit.and2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin)`.  Glue.

**Proof sketch.** `and2_eq`, `maxFanin_node` (arity `2`), `maxFaninL_cons` twice and
`maxFaninL_nil`; then `omega`. -/
theorem TreeCircuit.maxFanin_and2_le (a b : TreeCircuit n) :
    (TreeCircuit.and2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin) := by
  rw [TreeCircuit.and2_eq, TreeCircuit.maxFanin_node, TreeCircuit.maxFaninL_cons,
    TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_nil, List.length_cons, List.length_singleton]
  omega

/-- **F3, `or2`: value.** `(TreeCircuit.or2 a b).eval x = (a.eval x || b.eval x)`.  Glue.

**Proof sketch.** `or2_eq`, `eval_node_false`, and `List.any_cons`/`List.any_nil`. -/
theorem TreeCircuit.or2_eval (a b : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.or2 a b).eval x = (a.eval x || b.eval x) := by
  rw [TreeCircuit.or2_eq, TreeCircuit.eval_node_false, List.any_cons, List.any_cons, List.any_nil,
    Bool.or_false]

/-- **F3, `or2`: depth `+1`.** `(TreeCircuit.or2 a b).depth ≤ max a.depth b.depth + 1`.
Glue.

**Proof sketch.** As `depth_and2_le`, through `or2_eq`. -/
theorem TreeCircuit.depth_or2_le (a b : TreeCircuit n) :
    (TreeCircuit.or2 a b).depth ≤ max a.depth b.depth + 1 := by
  rw [TreeCircuit.or2_eq, TreeCircuit.depth_node, TreeCircuit.maxDepth_cons,
    TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_nil]
  omega

/-- **F3, `or2`: fan-in two.**
`(TreeCircuit.or2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin)`.  Glue.

**Proof sketch.** As `maxFanin_and2_le`, through `or2_eq`. -/
theorem TreeCircuit.maxFanin_or2_le (a b : TreeCircuit n) :
    (TreeCircuit.or2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin) := by
  rw [TreeCircuit.or2_eq, TreeCircuit.maxFanin_node, TreeCircuit.maxFaninL_cons,
    TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_nil, List.length_cons, List.length_singleton]
  omega

/-- **F3, `xor2`: value.** `(TreeCircuit.xor2 a b).eval x = (a.eval x ^^ b.eval x)`.  Glue.

**Proof sketch.** `xor2_eq`, `or2_eval`, `and2_eval` and `neg_eval`; then a case split on the
two Booleans. -/
theorem TreeCircuit.xor2_eval (a b : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.xor2 a b).eval x = (a.eval x ^^ b.eval x) := by
  rw [TreeCircuit.xor2_eq, TreeCircuit.or2_eval, TreeCircuit.and2_eval, TreeCircuit.and2_eval,
    TreeCircuit.neg_eval, TreeCircuit.neg_eval]
  cases a.eval x <;> cases b.eval x <;> rfl

/-- **F3, `xor2`: depth `+2`.** `(TreeCircuit.xor2 a b).depth ≤ max a.depth b.depth + 2`.
Glue; the constant `2` is settled by the construction (one `∧` level, one `∨` level, and the
depth-preserving `neg`).

**Proof sketch.** `xor2_eq`, `depth_or2_le`, `depth_and2_le` twice, and `depth_neg` for
`a.neg`, `b.neg`; then `omega`. -/
theorem TreeCircuit.depth_xor2_le (a b : TreeCircuit n) :
    (TreeCircuit.xor2 a b).depth ≤ max a.depth b.depth + 2 := by
  have h1 := TreeCircuit.depth_or2_le (TreeCircuit.and2 a b.neg) (TreeCircuit.and2 a.neg b)
  have h2 := TreeCircuit.depth_and2_le a b.neg
  have h3 := TreeCircuit.depth_and2_le a.neg b
  rw [TreeCircuit.depth_neg] at h2 h3
  rw [TreeCircuit.xor2_eq]
  omega

/-- **F3, `xor2`: fan-in two.**
`(TreeCircuit.xor2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin)`.  Glue.

**Proof sketch.** `xor2_eq`, `maxFanin_or2_le`, `maxFanin_and2_le` and `maxFanin_neg`; then
`omega`. -/
theorem TreeCircuit.maxFanin_xor2_le (a b : TreeCircuit n) :
    (TreeCircuit.xor2 a b).maxFanin ≤ max 2 (max a.maxFanin b.maxFanin) := by
  have h1 := TreeCircuit.maxFanin_or2_le (TreeCircuit.and2 a b.neg) (TreeCircuit.and2 a.neg b)
  have h2 := TreeCircuit.maxFanin_and2_le a b.neg
  have h3 := TreeCircuit.maxFanin_and2_le a.neg b
  rw [TreeCircuit.maxFanin_neg] at h2 h3
  rw [TreeCircuit.xor2_eq]
  omega

/-- **F3, `xor3`: value** (the full adder's sum bit).
`(TreeCircuit.xor3 a b c).eval x = (a.eval x ^^ b.eval x ^^ c.eval x)`.  Glue (r3 §H5.7, F3).

**Proof sketch.** `xor3_eq` and `xor2_eval` twice. -/
theorem TreeCircuit.xor3_eval (a b c : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.xor3 a b c).eval x = (a.eval x ^^ b.eval x ^^ c.eval x) := by
  rw [TreeCircuit.xor3_eq, TreeCircuit.xor2_eval, TreeCircuit.xor2_eval]

/-- **F3, `xor3`: depth `+4`.**
`(TreeCircuit.xor3 a b c).depth ≤ max a.depth (max b.depth c.depth) + 4`.  Glue; r3's `+4`
*(fix)*, settled by the construction: two nested `xor2`, each `+2`.

**Proof sketch.** `xor3_eq`, `depth_xor2_le` twice; then `omega`. -/
theorem TreeCircuit.depth_xor3_le (a b c : TreeCircuit n) :
    (TreeCircuit.xor3 a b c).depth ≤ max a.depth (max b.depth c.depth) + 4 := by
  have h1 := TreeCircuit.depth_xor2_le (TreeCircuit.xor2 a b) c
  have h2 := TreeCircuit.depth_xor2_le a b
  rw [TreeCircuit.xor3_eq]
  omega

/-- **F3, `xor3`: fan-in two.**
`(TreeCircuit.xor3 a b c).maxFanin ≤ max 2 (max a.maxFanin (max b.maxFanin c.maxFanin))`.
Glue.

**Proof sketch.** `xor3_eq` and `maxFanin_xor2_le` twice; then `omega`. -/
theorem TreeCircuit.maxFanin_xor3_le (a b c : TreeCircuit n) :
    (TreeCircuit.xor3 a b c).maxFanin ≤ max 2 (max a.maxFanin (max b.maxFanin c.maxFanin)) := by
  have h1 := TreeCircuit.maxFanin_xor2_le (TreeCircuit.xor2 a b) c
  have h2 := TreeCircuit.maxFanin_xor2_le a b
  rw [TreeCircuit.xor3_eq]
  omega

/-- **F3, `maj3`: value** (the full adder's carry bit, in the form of `carryBit`'s step).
`(TreeCircuit.maj3 a b c).eval x = (a.eval x && b.eval x || c.eval x && (a.eval x ^^ b.eval x))`.
Glue (r3 §H5.7, F3).  The formula computes `(a ∧ b) ∨ (c ∧ (a ∨ b))`, which is the same
Boolean function.

**Proof sketch.** `maj3_eq`, `or2_eval`, `and2_eval` twice and `or2_eval` again; then a case
split on the three Booleans. -/
theorem TreeCircuit.maj3_eval (a b c : TreeCircuit n) (x : Fin n → Bool) :
    (TreeCircuit.maj3 a b c).eval x =
      (a.eval x && b.eval x || c.eval x && (a.eval x ^^ b.eval x)) := by
  rw [TreeCircuit.maj3_eq, TreeCircuit.or2_eval, TreeCircuit.and2_eval, TreeCircuit.and2_eval,
    TreeCircuit.or2_eval]
  cases a.eval x <;> cases b.eval x <;> cases c.eval x <;> rfl

/-- **F3, `maj3`: depth `+3`.**
`(TreeCircuit.maj3 a b c).depth ≤ max a.depth (max b.depth c.depth) + 3`.  Glue; r3's `+3`
*(fix)*, settled by the construction `(a ∧ b) ∨ (c ∧ (a ∨ b))`.

**Proof sketch.** `maj3_eq`, `depth_or2_le` twice and `depth_and2_le` twice; then `omega`. -/
theorem TreeCircuit.depth_maj3_le (a b c : TreeCircuit n) :
    (TreeCircuit.maj3 a b c).depth ≤ max a.depth (max b.depth c.depth) + 3 := by
  have h1 := TreeCircuit.depth_or2_le (TreeCircuit.and2 a b)
    (TreeCircuit.and2 c (TreeCircuit.or2 a b))
  have h2 := TreeCircuit.depth_and2_le a b
  have h3 := TreeCircuit.depth_and2_le c (TreeCircuit.or2 a b)
  have h4 := TreeCircuit.depth_or2_le a b
  rw [TreeCircuit.maj3_eq]
  omega

/-- **F3, `maj3`: fan-in two.**
`(TreeCircuit.maj3 a b c).maxFanin ≤ max 2 (max a.maxFanin (max b.maxFanin c.maxFanin))`.
Glue.

**Proof sketch.** `maj3_eq`, `maxFanin_or2_le` twice and `maxFanin_and2_le` twice; then
`omega`. -/
theorem TreeCircuit.maxFanin_maj3_le (a b c : TreeCircuit n) :
    (TreeCircuit.maj3 a b c).maxFanin ≤ max 2 (max a.maxFanin (max b.maxFanin c.maxFanin)) := by
  have h1 := TreeCircuit.maxFanin_or2_le (TreeCircuit.and2 a b)
    (TreeCircuit.and2 c (TreeCircuit.or2 a b))
  have h2 := TreeCircuit.maxFanin_and2_le a b
  have h3 := TreeCircuit.maxFanin_and2_le c (TreeCircuit.or2 a b)
  have h4 := TreeCircuit.maxFanin_or2_le a b
  rw [TreeCircuit.maj3_eq]
  omega

end BoolCircuit
