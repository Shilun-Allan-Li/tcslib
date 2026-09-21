/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Function.Basic
-- POLICY EXCEPTION (policy.md §1, "import only what the file uses").  Nothing
-- below this file needs `Mathlib.Tactic`, but `TCSlib/BooleanAnalysis/LMN/*` and
-- `Switching/*` import this file as their only route to Mathlib: `aesop_cat`
-- (`LMN/CircuitHelpers.lean`), `Real.logb` (`LMN/IterativeReduction.lean`) and
-- `Real.rpow_natCast` (`LMN/BernoulliCost.lean`) all reach them through here.
-- Dropping it needs imports added to those files, which is out of scope here.
import Mathlib.Tactic

/-!
# Decision Trees

Binary decision trees with `eval`, `depth`, `deepPath`, the complete tree
`buildFullDTree`, and `dtDepth` (the minimum decision-tree depth computing a
given Boolean function).

## Main definitions

* `DecisionTree` — the tree type, with `eval` and `depth`.
* `DecisionTree.deepPath` — a deepest root-to-leaf path.
* `buildFullDTree` — the complete tree querying the variables in order.
* `dtDepth` — the least depth of a tree computing a given Boolean function.

## Main results

* `DecisionTree.length_deepPath` — the deep path has length the tree's depth.
* `buildFullDTree_depth` / `buildFullDTree_eval` — the complete tree has depth at
  most `n - k` and computes `f`; together they make `dtDepth` well defined.

## Divergences from [OD14, §3.2]

[OD14, Def 3.13] labels leaves by reals and forbids a coordinate from being
queried twice on a root-to-leaf path.  `DecisionTree` has `Bool` leaves and
imposes no no-repeat condition, so it ranges over strictly more trees than
[OD14] admits.  `dtDepth` is `Nat.find` on "some tree of depth at most `d`
computes `f`", the least depth of a computing tree *in that wider class*; no
theorem here relates it to [OD14]'s `DT(f)`.

## Provenance

Split out of `TCSlib/BooleanAnalysis/Switching/Circuit.lean` (commit 94fd7c6),
which carried no copyright header; `Authors` above is that file's git author.

## References

* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Decision Trees -/

/-- A decision tree on `n` Boolean variables.  [OD14, Def 3.13]
  - `leaf b`: output `b`.
  - `branch i lo hi`: query variable `i`; follow `lo` on `false`, `hi` on `true`. -/
inductive DecisionTree (n : ℕ) where
  | leaf   (val : Bool)                            : DecisionTree n
  | branch (var : Fin n) (lo hi : DecisionTree n) : DecisionTree n

/-- Evaluate decision tree `T` on input `x`. -/
def DecisionTree.eval {n : ℕ} : DecisionTree n → (Fin n → Bool) → Bool
  | .leaf b,          _  => b
  | .branch i lo hi,  x  => if x i then hi.eval x else lo.eval x

/-- Depth of a decision tree (maximum path length to a leaf).  [OD14, §3.2] -/
def DecisionTree.depth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _          => 0
  | .branch _ lo hi  => 1 + max lo.depth hi.depth

/-- Extract a deepest root-to-leaf path from a decision tree.
    At each branch, follows the deeper subtree (ties broken toward `hi`).
    Returns `(queried_variable, branch_direction)` pairs. -/
def DecisionTree.deepPath {n : ℕ} : DecisionTree n → List (Fin n × Bool)
  | .leaf _ => []
  | .branch v lo hi =>
    if hi.depth ≥ lo.depth then
      (v, true) :: hi.deepPath
    else
      (v, false) :: lo.deepPath

/-- The length of the deep path equals the tree's depth. -/
lemma DecisionTree.length_deepPath {n : ℕ} (T : DecisionTree n) :
    T.deepPath.length = T.depth := by
  induction T with
  | leaf _ => rfl
  | branch v lo hi ih_lo ih_hi =>
    simp only [deepPath]
    split
    · rename_i h
      simp only [List.length_cons, ih_hi, depth]
      omega
    · rename_i h
      simp only [List.length_cons, ih_lo, depth]
      omega

/-- Build a complete decision tree querying variables 0, 1, …, n−1 in order. -/
def buildFullDTree {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (acc : Fin n → Bool) : DecisionTree n :=
  if h : k < n then
    .branch ⟨k, h⟩
      (buildFullDTree f (k + 1) (Function.update acc ⟨k, h⟩ false))
      (buildFullDTree f (k + 1) (Function.update acc ⟨k, h⟩ true))
  else
    .leaf (f acc)
termination_by n - k

/-- The complete tree started at level `k` has depth at most `n - k`. -/
lemma buildFullDTree_depth {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (_ : k ≤ n) (acc : Fin n → Bool) :
    (buildFullDTree f k acc).depth ≤ n - k := by
  unfold buildFullDTree
  split
  · rename_i h
    simp only [DecisionTree.depth]
    have h1 := buildFullDTree_depth f (k + 1) (by omega)
      (Function.update acc ⟨k, h⟩ false)
    have h2 := buildFullDTree_depth f (k + 1) (by omega)
      (Function.update acc ⟨k, h⟩ true)
    have h3 := max_le h1 h2
    omega
  · simp [DecisionTree.depth]
termination_by n - k

/-- The complete tree computes `f` on every input it is consistent with.

**Proof sketch.** Induction on the number of variables still to be queried,
following the recursion that builds the tree.  The invariant carried along is
that the accumulator already agrees with the input on the coordinates queried so
far.  If variables remain, the tree branches on the next coordinate and
evaluation follows the branch named by the input's value there; updating the
accumulator at that coordinate to that same value extends the agreement by one
coordinate, which is exactly the hypothesis the induction step needs.  If none
remain, the tree is the leaf holding `f` of the accumulator, and the invariant
now covers every coordinate, so the accumulator and the input are equal as
functions and the leaf is `f` of the input. -/
lemma buildFullDTree_eval {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (hk : k ≤ n) (acc x : Fin n → Bool)
    (hinv : ∀ i : Fin n, i.val < k → acc i = x i) :
    (buildFullDTree f k acc).eval x = f x := by
  unfold buildFullDTree
  split
  · rename_i h
    simp only [DecisionTree.eval]
    cases hxv : x ⟨k, h⟩ with
    | false =>
      rw [if_neg (by decide : ¬(false = true))]
      apply buildFullDTree_eval f (k + 1) (by omega)
      intro i hi
      by_cases heq : i = ⟨k, h⟩
      · subst heq; simp [Function.update, hxv]
      · simp only [Function.update, heq]
        exact hinv i (by have : i.val ≠ k := fun hv => heq (Fin.ext hv); omega)
    | true =>
      rw [if_pos rfl]
      apply buildFullDTree_eval f (k + 1) (by omega)
      intro i hi
      by_cases heq : i = ⟨k, h⟩
      · subst heq; simp [Function.update, hxv]
      · simp only [Function.update, heq]
        exact hinv i (by have : i.val ≠ k := fun hv => heq (Fin.ext hv); omega)
  · simp only [DecisionTree.eval]
    have : acc = x := funext fun i => hinv i (by omega)
    rw [this]
termination_by n - k

/-- The minimum decision-tree depth to compute `f : (Fin n → Bool) → Bool`.
  [OD14, §3.2]
  Formally: `min { T.depth | T computes f }` =
  `Nat.sInf {d | ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x}`. -/
noncomputable def dtDepth {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x)
    ⟨n, buildFullDTree f 0 (fun _ => false),
     buildFullDTree_depth f 0 (Nat.zero_le n) _,
     fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
