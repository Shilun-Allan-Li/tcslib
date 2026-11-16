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
unchanged; `BoolCircuit.TreeCircuit.toBinary` now calls it from there.

## Main definitions

* `BoolCircuit.TreeCircuit.balanced` — the balanced binary tree of `b`-gates over a child list.

## Main results

* `BoolCircuit.TreeCircuit.balanced_eval` — it computes the unbounded gate.
* `BoolCircuit.TreeCircuit.maxFanin_balanced_le`, `depth_balanced_le`, `size_balanced_le` —
  fan-in two, `⌈log₂ |cs|⌉ + 1` extra depth, `|cs| + 1` extra size.
* `BoolCircuit.TreeCircuit.balanced_nil`, `balanced_singleton` — the readers on short lists.

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

end BoolCircuit
