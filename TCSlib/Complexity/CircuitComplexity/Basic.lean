/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.List.Nodup
-- Not used below.  This file's base-clause invariant is a `List.Nodup`, that is a
-- `List.Pairwise`, and `LMN/NormalFormConversion.lean` (which imports this file
-- and `Formulas.lean`, nothing else) reads it back through `List.Pairwise.forall`.
-- Of the 46 modules that transitively import this file that is the only one
-- affected: without this import `lake build` fails there, at line 144, and
-- nowhere else.
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Boolean Circuits: Literals and Circuit Trees

## Main definitions

* `BoolCircuit.Lit` — a literal: an index `idx : Fin n` and a sign
  (`sign = true` is the positive literal).
* `BoolCircuit.Circuit` — a Boolean circuit tree, `lit` or `node isAnd children`,
  with `eval`, `litCount`, `depth`, `size` and `maxFanin`.  Fan-in is unbounded; a
  bound is imposed downstream as a hypothesis `c.maxFanin ≤ w`, never as structure.
* `BoolCircuit.NAndCircuit` / `NOrCircuit` — normal-form circuits, strictly
  alternating AND/OR with a `Nodup` variable-index invariant at the base clauses.
* `BoolCircuit.Circuit.toNAnd` / `toNOr` — normalization into that form;
  `NAndCircuit.toCircuit` / `NOrCircuit.toCircuit` — the forgetful map back.

## Main results

* `Circuit.eval_lit`, `Circuit.eval_node_true_iff`, `Circuit.eval_node_false_iff`
  — the semantics of a leaf and of an unbounded AND / OR gate.
* `toNAnd_eval` / `toNOr_eval`, `toNAnd_litCount` / `toNOr_litCount`,
  `toNAnd_size_le` / `toNOr_size_le` — normalization preserves semantics and
  literal count, and at most doubles the size.

## Divergences from [OD14, §4.5]

`NAndCircuit` / `NOrCircuit` formalize [OD14, Def 4.26]'s alternating-layer
circuits, with [OD14, Def 4.27]'s condition that no base gate reads a variable
twice as the `Nodup` invariant.  `size` counts every node, leaves included, where
[OD14, Def 4.27] counts only the internal layers, and no width measure is defined
here — bottom-layer fan-in lives on `DNF` / `CNF` in `Formulas.lean`.  `Circuit`,
the unconstrained AND/OR tree, matches no numbered definition: [OD14]'s circuits
are DAGs.  `toNAnd` / `toNOr` are this library's own normalization; their
factor-2 size bound is proved here, not taken from [OD14]'s `2 ^ d` remark.

## Provenance

Split out of `TCSlib/BooleanAnalysis/Switching/Circuit.lean` (commit 94fd7c6),
which carried no copyright header; `Authors` above is that file's git author.
`DNF` / `CNF` live in `TCSlib.Complexity.CircuitComplexity.Formulas`, decision
trees in `...DecisionTree`, and the bridge from normal-form circuits to
`DNF` / `CNF` in `TCSlib.BooleanAnalysis.LMN.NormalFormConversion`.

## References

* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : Nat}

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

/-- A leaf evaluates to its literal. -/
theorem Circuit.eval_lit {n : Nat} (l : Lit n) (x : Fin n → Bool) :
    (Circuit.lit l).eval x = l.eval x := by
  simp [Circuit.eval]

/-- An unbounded `AND` gate is true exactly when every child is. -/
theorem Circuit.eval_node_true_iff {n : Nat} (cs : List (Circuit n)) (x : Fin n → Bool) :
    (Circuit.node true cs).eval x = true ↔ ∀ c ∈ cs, c.eval x = true := by
  simp only [Circuit.eval]
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

/-- An unbounded `OR` gate is true exactly when some child is. -/
theorem Circuit.eval_node_false_iff {n : Nat} (cs : List (Circuit n)) (x : Fin n → Bool) :
    (Circuit.node false cs).eval x = true ↔ ∃ c ∈ cs, c.eval x = true := by
  simp only [Circuit.eval]
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

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

/-- Maximum depth over a list of circuits (used in depth of a node). -/
def Circuit.maxDepth {n : Nat} (cs : List (Circuit n)) : Nat :=
  cs.foldr (fun c acc => max c.depth acc) 0

/-- Sum of sizes over a list of circuits (used in size of a node). -/
def Circuit.sumSize {n : Nat} (cs : List (Circuit n)) : Nat :=
  cs.foldr (fun c acc => c.size + acc) 0

/-- Maximum fanin of a circuit: maximum number of children of any gate, recursively. -/
def Circuit.maxFanin : Circuit n → Nat
  | .lit _ => 0
  | .node _ cs => max cs.length (cs.foldr (fun c acc => max c.maxFanin acc) 0)

-- ----------------------------------------------------------------
-- Section 3: Normal-form circuit (alternating, nodup at base)
-- ----------------------------------------------------------------

/-! The alternating normal form of [OD14, Def 4.26], with [OD14, Def 4.27]'s
condition that a base gate reads no variable twice, as the `Nodup` invariant. -/

mutual
/-- A normal-form circuit whose root is an `AND`: either a base `clause` of
    literals with pairwise distinct variable indices, or a `node` over
    `OR`-rooted children. -/
inductive NAndCircuit (n : Nat) where
  | clause : (lits : List (Lit n)) → (lits.map Lit.idx).Nodup → NAndCircuit n
  | node   : List (NOrCircuit n) → NAndCircuit n

/-- A normal-form circuit whose root is an `OR`: either a base `clause` of
    literals with pairwise distinct variable indices, or a `node` over
    `AND`-rooted children. -/
inductive NOrCircuit (n : Nat) where
  | clause : (lits : List (Lit n)) → (lits.map Lit.idx).Nodup → NOrCircuit n
  | node   : List (NAndCircuit n) → NOrCircuit n
end

-- Evaluation
mutual
/-- Evaluate an `AND`-rooted normal-form circuit: a clause is the conjunction of
    its literals, a node the conjunction of its children. -/
def NAndCircuit.eval : NAndCircuit n → (Fin n → Bool) → Bool
  | .clause lits _, x => lits.foldr (fun l acc => l.eval x && acc) true
  | .node cs, x       => cs.foldr (fun c acc => c.eval x && acc) true

/-- Evaluate an `OR`-rooted normal-form circuit: a clause is the disjunction of
    its literals, a node the disjunction of its children. -/
def NOrCircuit.eval : NOrCircuit n → (Fin n → Bool) → Bool
  | .clause lits _, x => lits.foldr (fun l acc => l.eval x || acc) false
  | .node cs, x       => cs.foldr (fun c acc => c.eval x || acc) false
end

-- Literal count
mutual
/-- Literal occurrences in an `AND`-rooted normal-form circuit: a clause's length,
    a node's the sum over its children. -/
def NAndCircuit.litCount : NAndCircuit n → Nat
  | .clause lits _ => lits.length
  | .node cs       => cs.foldr (fun c acc => c.litCount + acc) 0

/-- Literal occurrences in an `OR`-rooted normal-form circuit: a clause's length,
    a node's the sum over its children. -/
def NOrCircuit.litCount : NOrCircuit n → Nat
  | .clause lits _ => lits.length
  | .node cs       => cs.foldr (fun c acc => c.litCount + acc) 0
end

-- Total node count (size)
mutual
/-- Node count of an `AND`-rooted normal-form circuit: a clause is one node, a
    node one plus the sum over its children. -/
def NAndCircuit.size : NAndCircuit n → Nat
  | .clause _ _ => 1
  | .node cs    => 1 + cs.foldr (fun c acc => c.size + acc) 0

/-- Node count of an `OR`-rooted normal-form circuit: a clause is one node, a
    node one plus the sum over its children. -/
def NOrCircuit.size : NOrCircuit n → Nat
  | .clause _ _ => 1
  | .node cs    => 1 + cs.foldr (fun c acc => c.size + acc) 0
end

-- Depth
mutual
/-- Depth of an `AND`-rooted normal-form circuit: a clause has depth `0`, a node
    one more than its deepest child. -/
def NAndCircuit.depth : NAndCircuit n → Nat
  | .clause _ _ => 0
  | .node cs    => 1 + cs.foldr (fun c acc => max c.depth acc) 0

/-- Depth of an `OR`-rooted normal-form circuit: a clause has depth `0`, a node
    one more than its deepest child. -/
def NOrCircuit.depth : NOrCircuit n → Nat
  | .clause _ _ => 0
  | .node cs    => 1 + cs.foldr (fun c acc => max c.depth acc) 0
end

-- ----------------------------------------------------------------
-- Section 4: Properties that hold by construction (hnodup / hnd)
-- ----------------------------------------------------------------

/-- The `Nodup` invariant of an `AND`-rooted base clause, read back off the
    constructor. -/
theorem NAndCircuit.clause_nodup {n : Nat} {c : NAndCircuit n} {lits : List (Lit n)}
    {h : (lits.map Lit.idx).Nodup}
    (_ : c = NAndCircuit.clause lits h) : (lits.map Lit.idx).Nodup := h

/-- The `Nodup` invariant of an `OR`-rooted base clause, read back off the
    constructor. -/
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
/-- Normalize into `AND`-rooted alternating form: a leaf becomes a one-literal
    clause, an `AND` gate maps its children into `OR` form, and an `OR` gate
    becomes a one-child `AND` node over an `OR` node. -/
def Circuit.toNAnd : Circuit n → NAndCircuit n
  | .lit l          => .clause [l] (List.nodup_singleton _)
  | .node true  cs  => .node (cs.map Circuit.toNOr)
  | .node false cs  => .node [NOrCircuit.node (cs.map Circuit.toNAnd)]

/-- Normalize into `OR`-rooted alternating form: a leaf becomes a one-literal
    clause, an `OR` gate maps its children into `AND` form, and an `AND` gate
    becomes a one-child `OR` node over an `AND` node. -/
def Circuit.toNOr : Circuit n → NOrCircuit n
  | .lit l          => .clause [l] (List.nodup_singleton _)
  | .node false cs  => .node (cs.map Circuit.toNAnd)
  | .node true  cs  => .node [NAndCircuit.node (cs.map Circuit.toNOr)]
end

/-- Folding `&&` after `List.map h` agrees with folding `&&` directly, when
    `g (h c) = f c` on every element. -/
private theorem foldr_and_map {α β : Type*} {f : α → Bool} {g : β → Bool} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c && acc) true =
    cs.foldr (fun c acc => f c && acc) true := by
      induction cs <;> aesop

/-- Folding `||` after `List.map h` agrees with folding `||` directly, when
    `g (h c) = f c` on every element. -/
private theorem foldr_or_map {α β : Type*} {f : α → Bool} {g : β → Bool} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c || acc) false =
    cs.foldr (fun c acc => f c || acc) false := by
      induction cs <;> aesop

/-- Summing after `List.map h` agrees with summing directly, when
    `g (h c) = f c` on every element. -/
private theorem foldr_add_map {α β : Type*} {f : α → Nat} {g : β → Nat} {h : α → β}
    {cs : List α}
    (heq : ∀ c ∈ cs, g (h c) = f c) :
    (cs.map h).foldr (fun c acc => g c + acc) 0 =
    cs.foldr (fun c acc => f c + acc) 0 := by
      induction cs <;> aesop

/-- If `g (h c) ≤ k * f c` on every element, the sum after `List.map h` is at
    most `k` times the direct sum. -/
private theorem foldr_add_map_le {α β : Type*} {f : α → Nat} {g : β → Nat} {h : α → β}
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

/-- `toNAnd` preserves semantics. -/
theorem toNAnd_eval (c : Circuit n) (x : Fin n → Bool) :
    (c.toNAnd).eval x = c.eval x := (toNAnd_toNOr_eval c x).1

/-- `toNOr` preserves semantics. -/
theorem toNOr_eval (c : Circuit n) (x : Fin n → Bool) :
    (c.toNOr).eval x = c.eval x := (toNAnd_toNOr_eval c x).2

/-- Combined literal-count preservation.

**Proof sketch.** The two halves are proved together, by structural induction on
the circuit, because normalizing an AND gate calls the OR normalization on the
children and vice versa.  A leaf becomes a one-literal clause, so both counts are
`1`.  At a gate, one normalization maps the children directly and the other wraps
them in a single extra node; an extra node holds no literals, so in both cases
the count is the sum over the children of their normalized counts.  A side
induction on the child list then turns the induction hypothesis for each child
into equality of the two folded sums. -/
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

/-- `toNAnd` preserves the literal count. -/
theorem toNAnd_litCount (c : Circuit n) :
    (c.toNAnd).litCount = c.litCount := (toNAnd_toNOr_litCount c).1

/-- `toNOr` preserves the literal count. -/
theorem toNOr_litCount (c : Circuit n) :
    (c.toNOr).litCount = c.litCount := (toNAnd_toNOr_litCount c).2

/-- Combined size bound.

**Proof sketch.** Structural induction, again proving the two halves together.  A
leaf normalizes to a single clause: size one against a circuit of size one.  At a
gate, the normalization whose connective matches the gate maps the children
directly, giving size one plus the sum of the children's normalized sizes, while
the other inserts one node to restore alternation, giving two plus that sum.  The
step doing the work in each case is the list bound: if every child's normalized
size is at most twice its own, the sum of the normalized sizes is at most twice
the sum of the sizes.  The gate's own size is one more than the children's total,
so twice the gate's size leaves two units of slack over twice the children's
total — exactly enough to pay for the inserted node. -/
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

/-- `toNAnd` at most doubles the size. -/
theorem toNAnd_size_le (c : Circuit n) :
    (c.toNAnd).size ≤ 2 * c.size := (toNAnd_toNOr_size_le c).1

/-- `toNOr` at most doubles the size. -/
theorem toNOr_size_le (c : Circuit n) :
    (c.toNOr).size ≤ 2 * c.size := (toNAnd_toNOr_size_le c).2

-- ----------------------------------------------------------------
-- Section 6: Coercion: NCircuit → Circuit (forgetful map)
-- ----------------------------------------------------------------

mutual
/-- Forget the normal form: a clause becomes an `AND` gate over its literal
    leaves, a node an `AND` gate over its converted children. -/
def NAndCircuit.toCircuit : NAndCircuit n → Circuit n
  | .clause lits _ => .node true (lits.map fun l => .lit l)
  | .node cs       => .node true (cs.map NOrCircuit.toCircuit)

/-- Forget the normal form: a clause becomes an `OR` gate over its literal
    leaves, a node an `OR` gate over its converted children. -/
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
