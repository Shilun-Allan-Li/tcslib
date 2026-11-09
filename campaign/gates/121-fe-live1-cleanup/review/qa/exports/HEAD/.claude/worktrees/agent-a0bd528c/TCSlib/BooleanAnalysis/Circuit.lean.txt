-- import Mathlib.Data.Real.Basic
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.Data.Vector.Basic
-- import Mathlib.Algebra.MvPolynomial.Basic
-- import Mathlib.Algebra.MvPolynomial.Eval
-- import Mathlib.Data.ZMod.Basic
-- import Mathlib.Data.Fintype.Vector
-- import Mathlib.Data.Real.Sqrt
-- import Mathlib.Data.Fintype.Pi
-- import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Find


-- unbounded fan-in circuit
inductive Circuit (n : ℕ) where
  | input (i : Fin n)           : Circuit n
  | not   (c : Circuit n)       : Circuit n
  | and   (cs : List (Circuit n)) : Circuit n
  | or    (cs : List (Circuit n)) : Circuit n

namespace Circuit

/-
mutually recursive evaluation. "mutual" is needed so that Lean can suspend
the circular dependency rule. furthermore somehow Lean knows that this will
terminate.
-/
mutual
def eval {n : ℕ} (v : Vector Bool n) : Circuit n → Bool
  | input i => v.get i
  | not c   => !(eval v c)
  | and cs  => evalAnd v cs
  | or cs   => evalOr v cs

def evalAnd {n : ℕ} (v : Vector Bool n) : List (Circuit n) → Bool
  | [] => true --base case: this does not change output
  | c :: cs => eval v c && evalAnd v cs --kinda inefficient i guess.

def evalOr {n : ℕ} (v : Vector Bool n) : List (Circuit n) → Bool
  | [] => false
  | c :: cs => eval v c || evalOr v cs
end

-- mutually recursive depth calculation
mutual
def depth {n : ℕ} : Circuit n → ℕ
  | input _ => 0
  | not c   => depth c
  | and cs  => 1 + maxDepth cs
  | or cs   => 1 + maxDepth cs

def maxDepth {n : ℕ} : List (Circuit n) → ℕ
  | [] => 0
  | c :: cs => max (depth c) (maxDepth cs)
end

-- mutually recursive size calculation
mutual
def size {n : ℕ} : Circuit n → ℕ
  | input _ => 1
  | not c   => size c
  | and cs  => 1 + sumSize cs
  | or cs   => 1 + sumSize cs

def sumSize {n : ℕ} : List (Circuit n) → ℕ
  | [] => 0
  | c :: cs => size c + sumSize cs
end

end Circuit

/-! ## Literals, Terms, and DNF/CNF formulas -/

/-- A literal: variable `var : Fin n` with polarity `neg` (true = negated literal). -/
structure Literal (n : ℕ) where
  var : Fin n
  neg : Bool
  deriving DecidableEq

/-- Evaluate literal `l` on input `x`: positive literal returns `x i`, negated returns `¬(x i)`. -/
def Literal.eval {n : ℕ} (l : Literal n) (x : Fin n → Bool) : Bool :=
  if l.neg then !x l.var else x l.var

/-- A term is a conjunction of literals. -/
abbrev Term (n : ℕ) := List (Literal n)

/-- Width of a term (number of literals). -/
def Term.width {n : ℕ} (t : Term n) : ℕ := t.length

/-- Evaluate term `t` as a conjunction: all literals must hold. -/
def Term.eval {n : ℕ} (t : Term n) (x : Fin n → Bool) : Bool :=
  t.all (fun l => l.eval x)

/-- A DNF formula is a disjunction of terms. -/
abbrev DNF (n : ℕ) := List (Term n)

/-- Width of a DNF formula (maximum term width; 0 for empty). -/
def DNF.width {n : ℕ} (d : DNF n) : ℕ := (d.map Term.width).foldr max 0

/-- Evaluate DNF `d`: at least one term must hold. -/
def DNF.eval {n : ℕ} (d : DNF n) (x : Fin n → Bool) : Bool :=
  d.any (fun t => t.eval x)

/-- A CNF formula is a conjunction of clauses, each a disjunction of literals. -/
abbrev CNF (n : ℕ) := List (Term n)

/-- Width of a CNF formula (maximum clause width). -/
def CNF.width {n : ℕ} (c : CNF n) : ℕ := (c.map Term.width).foldr max 0

/-- Evaluate a single clause as a disjunction: some literal must hold. -/
def CNF.evalClause {n : ℕ} (t : Term n) (x : Fin n → Bool) : Bool :=
  t.any (fun l => l.eval x)

/-- Evaluate CNF `c`: all clauses must hold. -/
def CNF.eval {n : ℕ} (c : CNF n) (x : Fin n → Bool) : Bool :=
  c.all (fun t => CNF.evalClause t x)

/-! ## Decision Trees -/

/-- A decision tree on `n` Boolean variables.
  - `leaf b`: output `b`.
  - `branch i lo hi`: query variable `i`; follow `lo` on `false`, `hi` on `true`. -/
inductive DecisionTree (n : ℕ) where
  | leaf   (val : Bool)                            : DecisionTree n
  | branch (var : Fin n) (lo hi : DecisionTree n) : DecisionTree n

/-- Evaluate decision tree `T` on input `x`. -/
def DecisionTree.eval {n : ℕ} : DecisionTree n → (Fin n → Bool) → Bool
  | .leaf b,          _  => b
  | .branch i lo hi,  x  => if x i then hi.eval x else lo.eval x

/-- Depth of a decision tree (maximum path length to a leaf). -/
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
  Formally: `min { T.depth | T computes f }` =
  `Nat.sInf {d | ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x}`. -/
noncomputable def dtDepth {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x)
    ⟨n, buildFullDTree f 0 (fun _ => false),
     buildFullDTree_depth f 0 (Nat.zero_le n) _,
     fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
