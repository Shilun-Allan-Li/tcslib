import Mathlib

/-!
# Boolean Circuits, Literals, Terms, DNF/CNF, Decision Trees

This file provides:

1. **`BoolCircuit.Lit`**: A literal with `idx : Fin n` and `sign : Bool`
   (`sign = true` = positive literal).

2. **`BoolCircuit.Circuit`**: A general Boolean circuit tree with `lit` and
   `node isAnd children` constructors, together with `eval`, `litCount`, `depth`,
   and `size`.

3. **`BoolCircuit.NAndCircuit` / `NOrCircuit`**: Normal-form circuits with
   strictly alternating AND/OR gates and `Nodup` variable-index invariant at the
   base clause level.  Includes normalization maps `toNAnd` / `toNOr` with proofs
   of semantics preservation, literal-count preservation, and size bounds.

4. **`Literal` / `Term` / `DNF` / `CNF`**: Types used in the switching-lemma
   proof (kept for backward compatibility).

5. **`DecisionTree`**: Binary decision trees with `eval`, `depth`, `deepPath`,
   and `dtDepth` (minimum DT depth).
-/

set_option maxHeartbeats 800000

-- ================================================================
-- Part A: BoolCircuit namespace (from BooleanAnalysis/Circuit.lean)
-- ================================================================

namespace BoolCircuit

-- ----------------------------------------------------------------
-- Section 1: Literals
-- ----------------------------------------------------------------

/-- A literal on `n` Boolean variables: a variable index together with a sign.
    `sign = true` means the positive literal xᵢ; `sign = false` means ¬xᵢ. -/
structure Lit (n : Nat) where
  idx : Fin n
  sign : Bool
deriving DecidableEq, Repr, Hashable

/-- Evaluate a literal under assignment `x`. -/
@[simp]
def Lit.eval (l : Lit n) (x : Fin n → Bool) : Bool :=
  if l.sign then x l.idx else !x l.idx

-- ----------------------------------------------------------------
-- Section 2: General (unconstrained) circuit
-- ----------------------------------------------------------------

/-- A Boolean circuit tree on `n` variables.
    - `lit l` is a single literal.
    - `node isAnd children` applies an AND gate (`isAnd = true`) or OR gate
      (`isAnd = false`) to its children.
    No alternation or deduplication constraint is imposed. -/
inductive Circuit (n : Nat) where
  | lit  : Lit n → Circuit n
  | node : (isAnd : Bool) → List (Circuit n) → Circuit n
deriving Repr

/-- Custom induction principle for `Circuit` that gives `∀ c ∈ cs, motive c` in the
    `node` case, working around the limitation that `induction` doesn't support
    nested inductives directly. -/
theorem Circuit.ind {n : Nat} {motive : Circuit n → Prop}
    (hlit : ∀ l, motive (.lit l))
    (hnode : ∀ isAnd cs, (∀ c ∈ cs, motive c) → motive (.node isAnd cs)) :
    ∀ c, motive c :=
  @Circuit.rec n motive (fun cs => ∀ c ∈ cs, motive c)
    hlit
    (fun isAnd cs ih => hnode isAnd cs ih)
    (fun _ h => nomatch h)
    (fun head tail ih_head ih_tail c hc => by
      cases hc with
      | head => exact ih_head
      | tail _ h => exact ih_tail c h)

/-- Evaluate a general circuit under assignment `x`. -/
def Circuit.eval : Circuit n → (Fin n → Bool) → Bool
  | .lit l, x => l.eval x
  | .node true cs, x  => cs.foldr (fun c acc => c.eval x && acc) true
  | .node false cs, x => cs.foldr (fun c acc => c.eval x || acc) false

/-- Number of literal occurrences in a circuit. -/
def Circuit.litCount : Circuit n → Nat
  | .lit _ => 1
  | .node _ cs => cs.foldr (fun c acc => c.litCount + acc) 0

/-- Depth of a circuit (longest root-to-leaf path). -/
def Circuit.depth : Circuit n → Nat
  | .lit _ => 0
  | .node _ cs => 1 + cs.foldr (fun c acc => max c.depth acc) 0

/-- Total number of nodes (internal gates + literal leaves). -/
def Circuit.size : Circuit n → Nat
  | .lit _ => 1
  | .node _ cs => 1 + cs.foldr (fun c acc => c.size + acc) 0

-- ----------------------------------------------------------------
-- Section 3: Normal-form circuit (alternating, nodup at base)
-- ----------------------------------------------------------------

mutual
inductive NAndCircuit (n : Nat) where
  | clause : (lits : List (Lit n)) → (lits.map Lit.idx).Nodup → NAndCircuit n
  | node   : List (NOrCircuit n) → NAndCircuit n

inductive NOrCircuit (n : Nat) where
  | clause : (lits : List (Lit n)) → (lits.map Lit.idx).Nodup → NOrCircuit n
  | node   : List (NAndCircuit n) → NOrCircuit n
end

-- Evaluation
mutual
def NAndCircuit.eval : NAndCircuit n → (Fin n → Bool) → Bool
  | .clause lits _, x => lits.foldr (fun l acc => l.eval x && acc) true
  | .node cs, x       => cs.foldr (fun c acc => c.eval x && acc) true

def NOrCircuit.eval : NOrCircuit n → (Fin n → Bool) → Bool
  | .clause lits _, x => lits.foldr (fun l acc => l.eval x || acc) false
  | .node cs, x       => cs.foldr (fun c acc => c.eval x || acc) false
end

-- Literal count
mutual
def NAndCircuit.litCount : NAndCircuit n → Nat
  | .clause lits _ => lits.length
  | .node cs       => cs.foldr (fun c acc => c.litCount + acc) 0

def NOrCircuit.litCount : NOrCircuit n → Nat
  | .clause lits _ => lits.length
  | .node cs       => cs.foldr (fun c acc => c.litCount + acc) 0
end

-- Total node count (size)
mutual
def NAndCircuit.size : NAndCircuit n → Nat
  | .clause _ _ => 1
  | .node cs    => 1 + cs.foldr (fun c acc => c.size + acc) 0

def NOrCircuit.size : NOrCircuit n → Nat
  | .clause _ _ => 1
  | .node cs    => 1 + cs.foldr (fun c acc => c.size + acc) 0
end

-- Depth
mutual
def NAndCircuit.depth : NAndCircuit n → Nat
  | .clause _ _ => 0
  | .node cs    => 1 + cs.foldr (fun c acc => max c.depth acc) 0

def NOrCircuit.depth : NOrCircuit n → Nat
  | .clause _ _ => 0
  | .node cs    => 1 + cs.foldr (fun c acc => max c.depth acc) 0
end

-- ----------------------------------------------------------------
-- Section 4: Properties that hold by construction (hnodup / hnd)
-- ----------------------------------------------------------------

theorem NAndCircuit.clause_nodup {n : Nat} {c : NAndCircuit n} {lits : List (Lit n)}
    {h : (lits.map Lit.idx).Nodup}
    (_ : c = NAndCircuit.clause lits h) : (lits.map Lit.idx).Nodup := h

theorem NOrCircuit.clause_nodup {n : Nat} {c : NOrCircuit n} {lits : List (Lit n)}
    {h : (lits.map Lit.idx).Nodup}
    (_ : c = NOrCircuit.clause lits h) : (lits.map Lit.idx).Nodup := h

/-- In every clause of a normal-form circuit, if two literals share the same
    variable index then they are identical. -/
theorem Lit.eq_of_idx_eq_of_mem_nodup
    {lits : List (Lit n)} (hnd : (lits.map Lit.idx).Nodup)
    {l₁ l₂ : Lit n} (h₁ : l₁ ∈ lits) (h₂ : l₂ ∈ lits) (hidx : l₁.idx = l₂.idx) :
    l₁ = l₂ := by
      have := List.nodup_iff_injective_get.mp hnd
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h₁
      obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp h₂
      simp_all +decide
      have := @this ⟨ i, by simp ⟩ ⟨ j, by simp ⟩
      aesop

-- ----------------------------------------------------------------
-- Section 5: Normalization : Circuit → Normal-form circuit
-- ----------------------------------------------------------------

mutual
def Circuit.toNAnd : Circuit n → NAndCircuit n
  | .lit l          => .clause [l] (List.nodup_singleton _)
  | .node true  cs  => .node (cs.map Circuit.toNOr)
  | .node false cs  => .node [NOrCircuit.node (cs.map Circuit.toNAnd)]

def Circuit.toNOr : Circuit n → NOrCircuit n
  | .lit l          => .clause [l] (List.nodup_singleton _)
  | .node false cs  => .node (cs.map Circuit.toNAnd)
  | .node true  cs  => .node [NAndCircuit.node (cs.map Circuit.toNOr)]
end

private theorem foldr_and_map {f : α → Bool} {g : β → Bool} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c && acc) true =
    cs.foldr (fun c acc => f c && acc) true := by
      induction cs <;> aesop

private theorem foldr_or_map {f : α → Bool} {g : β → Bool} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c || acc) false =
    cs.foldr (fun c acc => f c || acc) false := by
      induction cs <;> aesop

private theorem foldr_add_map {f : α → Nat} {g : β → Nat} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c + acc) 0 =
    cs.foldr (fun c acc => f c + acc) 0 := by
      induction cs <;> aesop

private theorem foldr_add_map_le {f : α → Nat} {g : β → Nat} {h : α → β}
    {cs : List α} {k : Nat}
    (heq : ∀ c ∈ cs, g (h c) ≤ k * f c) :
    (cs.map h).foldr (fun c acc => g c + acc) 0 ≤
    k * cs.foldr (fun c acc => f c + acc) 0 := by
      induction' cs with c cs ih
      · simp +decide
      · simp +zetaDelta at *
        linarith [ ih heq.2 ]

/-- Combined semantics preservation theorem (proves both toNAnd and toNOr at once). -/
theorem toNAnd_toNOr_eval (c : Circuit n) (x : Fin n → Bool) :
    (c.toNAnd).eval x = c.eval x ∧ (c.toNOr).eval x = c.eval x := by
      induction' c using Circuit.ind with l isAnd cs ih
      · repeat' unfold Circuit.toNAnd Circuit.toNOr
        unfold NAndCircuit.eval NOrCircuit.eval Circuit.eval; aesop
      · unfold Circuit.toNAnd Circuit.toNOr Circuit.eval
        cases isAnd <;> simp +decide [ * ]
        · simp [NAndCircuit.eval]
          unfold NOrCircuit.eval; simp +decide [ List.foldr_map ]
          induction cs <;> aesop
        · unfold NOrCircuit.eval; simp +decide
          unfold NAndCircuit.eval
          induction cs <;> aesop

theorem toNAnd_eval (c : Circuit n) (x : Fin n → Bool) :
    (c.toNAnd).eval x = c.eval x := (toNAnd_toNOr_eval c x).1

theorem toNOr_eval (c : Circuit n) (x : Fin n → Bool) :
    (c.toNOr).eval x = c.eval x := (toNAnd_toNOr_eval c x).2

/-- Combined literal-count preservation. -/
theorem toNAnd_toNOr_litCount (c : Circuit n) :
    (c.toNAnd).litCount = c.litCount ∧ (c.toNOr).litCount = c.litCount := by
      by_contra h_contra
      revert h_contra
      induction' c using Circuit.ind with l isAnd cs ih
      · unfold Circuit.toNAnd Circuit.toNOr
        unfold NAndCircuit.litCount NOrCircuit.litCount Circuit.litCount; aesop
      · cases isAnd <;> simp_all +decide
        · unfold Circuit.toNAnd Circuit.toNOr
          unfold NAndCircuit.litCount NOrCircuit.litCount Circuit.litCount
          induction cs <;> simp_all +decide [ List.foldr ]
        · unfold Circuit.toNAnd Circuit.toNOr
          constructor
          · unfold NAndCircuit.litCount Circuit.litCount
            have h_foldr : ∀ (cs : List (Circuit n)),
                (∀ c ∈ cs, c.toNOr.litCount = c.litCount) →
                List.foldr (fun c acc => c.litCount + acc) 0 (List.map Circuit.toNOr cs) =
                List.foldr (fun c acc => c.litCount + acc) 0 cs := by
              intros cs hcs; induction cs <;> aesop
            exact h_foldr cs fun c hc => ih c hc |>.2
          · unfold NOrCircuit.litCount Circuit.litCount; simp +decide
            unfold NAndCircuit.litCount
            have h_foldr : ∀ (cs : List (Circuit n)),
                (∀ c ∈ cs, c.toNOr.litCount = c.litCount) →
                List.foldr (fun c acc => c.litCount + acc) 0 (List.map Circuit.toNOr cs) =
                List.foldr (fun c acc => c.litCount + acc) 0 cs := by
              intros cs hcs; induction cs <;> aesop
            exact h_foldr cs fun c hc => ih c hc |>.2

theorem toNAnd_litCount (c : Circuit n) :
    (c.toNAnd).litCount = c.litCount := (toNAnd_toNOr_litCount c).1

theorem toNOr_litCount (c : Circuit n) :
    (c.toNOr).litCount = c.litCount := (toNAnd_toNOr_litCount c).2

/-- Combined size bound. -/
theorem toNAnd_toNOr_size_le (c : Circuit n) :
    (c.toNAnd).size ≤ 2 * c.size ∧ (c.toNOr).size ≤ 2 * c.size := by
      induction' c using Circuit.ind with l isAnd cs ih
      · simp +arith +decide [ Circuit.toNAnd, Circuit.toNOr ]
        exact ⟨ by simp +arith +decide [ NAndCircuit.size, Circuit.size ],
                by simp +arith +decide [ NOrCircuit.size, Circuit.size ] ⟩
      · have h_ind : ∀ c ∈ cs, c.toNAnd.size ≤ 2 * c.size ∧ c.toNOr.size ≤ 2 * c.size :=
          ih
        unfold Circuit.toNAnd Circuit.toNOr Circuit.size
        cases isAnd <;> simp +decide [ * ]
        · constructor
          · simp +arith +decide [ NAndCircuit.size ]
            unfold NOrCircuit.size; simp +arith +decide [ * ]
            have h_foldr : ∀ (cs : List (Circuit n)),
                (∀ c ∈ cs, c.toNAnd.size ≤ 2 * c.size) →
                List.foldr (fun c acc => acc + c.size) 0 (List.map Circuit.toNAnd cs) ≤
                2 * List.foldr (fun c acc => acc + c.size) 0 cs := by
              intro cs h_ind; induction cs <;> simp_all +decide [ mul_add ]
              grind
            exact h_foldr cs fun c hc => h_ind c hc |>.1
          · unfold NOrCircuit.size
            have h_foldr :
                List.foldr (fun c acc => c.size + acc) 0 (List.map Circuit.toNAnd cs) ≤
                2 * List.foldr (fun c acc => c.size + acc) 0 cs := by
              convert foldr_add_map_le _ using 1
              exact fun c hc => h_ind c hc |>.1
            linarith
        · have h_node :
              (List.foldr (fun c acc => c.toNOr.size + acc) 0 cs) ≤
              2 * (List.foldr (fun c acc => c.size + acc) 0 cs) := by
            have h_node : ∀ (cs : List (Circuit n)),
                (∀ c ∈ cs, c.toNOr.size ≤ 2 * c.size) →
                (List.foldr (fun c acc => c.toNOr.size + acc) 0 cs) ≤
                2 * (List.foldr (fun c acc => c.size + acc) 0 cs) := by
              intros cs hcs; induction cs <;> simp_all +decide [ mul_add ]
              linarith
            exact h_node cs fun c hc => h_ind c hc |>.2
          constructor
          · unfold NAndCircuit.size; simp +arith +decide [ * ]
            convert Nat.le_succ_of_le h_node using 1
            · clear h_ind h_node ih
              induction cs <;> simp +decide [ * ]
              ring
            · simp +arith +decide [ add_comm ]
          · simp +arith +decide [ NOrCircuit.size ]
            simp +arith +decide [ NAndCircuit.size ]
            convert h_node using 1
            · clear h_ind h_node ih
              induction cs <;> simp +decide [ * ]
              ring
            · ac_rfl

theorem toNAnd_size_le (c : Circuit n) :
    (c.toNAnd).size ≤ 2 * c.size := (toNAnd_toNOr_size_le c).1

theorem toNOr_size_le (c : Circuit n) :
    (c.toNOr).size ≤ 2 * c.size := (toNAnd_toNOr_size_le c).2

-- ----------------------------------------------------------------
-- Section 6: Coercion: NCircuit → Circuit (forgetful map)
-- ----------------------------------------------------------------

mutual
def NAndCircuit.toCircuit : NAndCircuit n → Circuit n
  | .clause lits _ => .node true (lits.map fun l => .lit l)
  | .node cs       => .node true (cs.map NOrCircuit.toCircuit)

def NOrCircuit.toCircuit : NOrCircuit n → Circuit n
  | .clause lits _ => .node false (lits.map fun l => .lit l)
  | .node cs       => .node false (cs.map NAndCircuit.toCircuit)
end

-- ----------------------------------------------------------------
-- Section 7: Useful derived API
-- ----------------------------------------------------------------

/-- Build a single-variable AND-circuit. -/
def NAndCircuit.ofVar (i : Fin n) : NAndCircuit n :=
  .clause [⟨i, true⟩] (List.nodup_singleton _)

/-- Build a single-variable OR-circuit. -/
def NOrCircuit.ofVar (i : Fin n) : NOrCircuit n :=
  .clause [⟨i, true⟩] (List.nodup_singleton _)

/-- The constant-true AND-circuit (empty conjunction). -/
def NAndCircuit.constTrue : NAndCircuit n :=
  .clause [] List.nodup_nil

/-- The constant-false OR-circuit (empty disjunction). -/
def NOrCircuit.constFalse : NOrCircuit n :=
  .clause [] List.nodup_nil

end BoolCircuit

-- ================================================================
-- Part B: Switching-lemma infrastructure (unchanged)
-- ================================================================

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
