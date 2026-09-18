/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.NPReductions.SATTo3SAT

/-!
# CKT-SAT, and the Tseitin reduction to 3SAT

Arora–Barak Definition 6.9 and Lemma 6.11.

## Main definitions

* `BoolCircuit.Circuit.Satisfiable`, `BoolCircuit.CktSat` — [AB09, Def 6.9].
* `BoolCircuit.CktVar` — the Tseitin variables: one per input, one per subcircuit.
* `BoolCircuit.Circuit.toCNF` — the gate clauses plus the output unit clause.

## Main results

* `BoolCircuit.Circuit.satisfiable_iff_isSatisfiable` — both directions of
  [AB09, Lem 6.11], before the 3-CNF step.
* `BoolCircuit.mem_cktSat_iff_is3Satisfiable` — [AB09, Lem 6.11], equisatisfiability only.
* `BoolCircuit.Circuit.toCNF_length_le` — the intermediate `C.toCNF` has at most
  `3 * C.size` clauses.

## Divergences from Arora–Barak §6.1.2

Only equisatisfiability is formalized, not `≤p`: TCSlib has no machine model, and this
file proves no bound on the reduction's cost. `toCNF_length_le` counts the clauses of the
intermediate `C.toCNF` and no more — clause *width* is unbounded (see fan-in below),
and `CktVar n`, indexed by all of `Circuit n`, is infinite, so the output formula has no
bit length here.  Relatedly, AB's CKT-SAT is a language of *strings representing*
circuits, whereas `CktSat` is a set of circuits: the Tseitin proof must not depend on an
encoding.  `CircuitComplexity.Encoding` supplies one downstream, and with it a clause
count bounded in the encoded input length — still not a `≤p` claim.

Model: `BoolCircuit.Circuit`, a tree, not the DAG `ACP.FeedForward` of `PPoly.lean`. The
tree is forced, though not for the reason earlier drafts of this file gave: a gate's
membership in these gate sets *can* be cased on: `ACP.ACp_GateOps_cases`
(`ACpGates.lean:585`) does it for `ACp_GateOps p`, unfolding the `⋃` through
`Set.mem_iUnion.mp`, and `ACp_GateOps = AC_GateOps ∪ ⋃ n, {modGateOp p n}` — no
`AC_GateOps_cases` exists, but nothing obstructs one.  What blocks a clause map over
`FeedForward` is that `AC_GateOps` contains `id` and `NOT`, for which `Circuit` has no
node, and that `FeedForward.nodes` is an arbitrary type family with nothing to index
Tseitin variables by.  No equivalence of the two models is claimed, and none is
available here. `Circuit` has no `NOT` gate — negation
lives in the leaf literals — so AB's `zᵢ ↔ ¬z_j` pair occurs exactly at a negative leaf.

Fan-in stays unbounded, as in `PPoly.lean`, so a width-`w` `AND` needs one clause of
width `w + 1` and `toCNF` is CNF, not 3-CNF; rather than pre-reduce to fan-in 2 we
compose with `SATTo3SAT.to3SAT`. Equal subcircuits share a variable — Tseitin sharing.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

open SATTo3SAT

variable {n : ℕ}

/-! ## CKT-SAT -/

/-- A circuit is satisfiable when some input makes it output `true`. -/
def Circuit.Satisfiable (C : Circuit n) : Prop :=
  ∃ u : Fin n → Bool, C.eval u = true

/-- CKT-SAT: the satisfiable circuits, indexed by their arity.  [AB09, Def 6.9] -/
def CktSat : Set ((n : ℕ) × Circuit n) :=
  {C | C.2.Satisfiable}

/-- Membership in `CktSat` is satisfiability of the underlying circuit. -/
@[simp]
theorem mem_cktSat_iff (C : (n : ℕ) × Circuit n) : C ∈ CktSat ↔ C.2.Satisfiable :=
  Iff.rfl

/-! `CktSat` is neither empty nor everything: on zero inputs the empty `AND` is
satisfiable and the empty `OR` is not. -/

example : (⟨0, .node true []⟩ : (n : ℕ) × Circuit n) ∈ CktSat :=
  ⟨finZeroElim, by simp [Circuit.eval]⟩

example : (⟨0, .node false []⟩ : (n : ℕ) × Circuit n) ∉ CktSat := by
  rintro ⟨u, hu⟩
  simp [Circuit.eval] at hu

/-! ## The Tseitin encoding -/

/-- The variables of the encoding: the circuit's inputs, and one per subcircuit. -/
inductive CktVar (n : ℕ) where
  | input : Fin n → CktVar n
  | gate : Circuit n → CktVar n

/-- The literal over `CktVar n` that holds exactly when the leaf literal `l` does. -/
def Lit.toCktLiteral (l : Lit n) : Literal (CktVar n) :=
  if l.sign then .pos (.input l.idx) else .neg (.input l.idx)

/-- The negation of `Lit.toCktLiteral l`. -/
def Lit.toCktLiteralNeg (l : Lit n) : Literal (CktVar n) :=
  if l.sign then .neg (.input l.idx) else .pos (.input l.idx)

/-- The clauses forcing `z ↔ ⋀ zᵢ` (`isAnd = true`) or `z ↔ ⋁ zᵢ`, where `z` is the
variable of `node isAnd cs` and the `zᵢ` are those of its children. -/
def gateClauses : Bool → List (Circuit n) → CNFFormula (CktVar n)
  | true, cs =>
      (Literal.pos (.gate (.node true cs)) :: cs.map fun c => Literal.neg (.gate c)) ::
        cs.map fun c => [Literal.neg (.gate (.node true cs)), Literal.pos (.gate c)]
  | false, cs =>
      (Literal.neg (.gate (.node false cs)) :: cs.map fun c => Literal.pos (.gate c)) ::
        cs.map fun c => [Literal.pos (.gate (.node false cs)), Literal.neg (.gate c)]

/-- The gate clauses of every subcircuit of `C`. -/
def Circuit.tseitin : Circuit n → CNFFormula (CktVar n)
  | .lit l =>
      [[Literal.neg (.gate (.lit l)), l.toCktLiteral],
       [Literal.pos (.gate (.lit l)), l.toCktLiteralNeg]]
  | .node b cs => gateClauses b cs ++ cs.flatMap fun c => c.tseitin

/-- The CNF formula the reduction produces: the gate clauses together with the unit
clause on the output node. -/
def Circuit.toCNF (C : Circuit n) : CNFFormula (CktVar n) :=
  [Literal.pos (.gate C)] :: C.tseitin

/-- The assignment reading the inputs off `u` and every subcircuit variable off that
subcircuit's value. -/
def tseitinAssignment (u : Fin n → Bool) : CktVar n → Prop
  | .input i => u i = true
  | .gate D => D.eval u = true

/-! ## Correctness -/

/-- A leaf literal's translation holds exactly when the leaf literal does. -/
theorem evalLiteral_toCktLiteral_iff {α : Assignment (CktVar n)} {u : Fin n → Bool}
    (hu : ∀ i, u i = true ↔ α (CktVar.input i)) (l : Lit n) :
    evalLiteral α l.toCktLiteral ↔ l.eval u = true := by
  cases hs : l.sign <;> cases hb : u l.idx <;>
    simp [Lit.toCktLiteral, evalLiteral, hs, hb, ← hu l.idx]

/-- `Lit.toCktLiteralNeg` translates the negation of a leaf literal. -/
theorem evalLiteral_toCktLiteralNeg_iff {α : Assignment (CktVar n)} {u : Fin n → Bool}
    (hu : ∀ i, u i = true ↔ α (CktVar.input i)) (l : Lit n) :
    evalLiteral α l.toCktLiteralNeg ↔ ¬ (l.eval u = true) := by
  cases hs : l.sign <;> cases hb : u l.idx <;>
    simp [Lit.toCktLiteralNeg, evalLiteral, hs, hb, ← hu l.idx]

/-- The canonical assignment satisfies the clauses of any one gate.

**Proof sketch.** Split on the gate's connective; the two cases are dual, with
every polarity exchanged.  Take the OR gate.  Its clause set is one long clause
saying that if the gate's variable holds then some child's does, together with
one short clause per child saying the converse for that child.  For the long
clause, ask whether the gate evaluates to true under the given input: if it
does, the unbounded OR semantics hand back a child that evaluates to true and
that child's positive literal is satisfied; if it does not, the gate's own
negative literal is.  For the short clause of a child, ask whether that child
evaluates to true: if it does, so does the gate, satisfying the gate's positive
literal; if it does not, the child's negative literal is satisfied.  In the AND
case the witness for the long clause in the false branch is a child that fails,
obtained by contraposing the unbounded AND semantics. -/
theorem gateClauses_satisfied (u : Fin n → Bool) (b : Bool) (cs : List (Circuit n)) :
    formulaSatisfied (tseitinAssignment u) (gateClauses b cs) := by
  cases b
  · intro c hc
    simp only [gateClauses, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨d, hd, rfl⟩
    · by_cases hz : (Circuit.node false cs).eval u = true
      · obtain ⟨d, hd, hdv⟩ := (Circuit.eval_node_false_iff cs u).mp hz
        exact ⟨Literal.pos (.gate d),
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hd, rfl⟩), hdv⟩
      · exact ⟨Literal.neg (.gate (.node false cs)), List.mem_cons_self, hz⟩
    · by_cases hdv : d.eval u = true
      · exact ⟨Literal.pos (.gate (.node false cs)), List.mem_cons_self,
          (Circuit.eval_node_false_iff cs u).mpr ⟨d, hd, hdv⟩⟩
      · exact ⟨Literal.neg (.gate d), List.mem_cons_of_mem _ List.mem_cons_self, hdv⟩
  · intro c hc
    simp only [gateClauses, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨d, hd, rfl⟩
    · by_cases hz : (Circuit.node true cs).eval u = true
      · exact ⟨Literal.pos (.gate (.node true cs)), List.mem_cons_self, hz⟩
      · obtain ⟨d, hd, hdv⟩ : ∃ d ∈ cs, ¬ d.eval u = true := by
          by_contra hcon
          push_neg at hcon
          exact hz ((Circuit.eval_node_true_iff cs u).mpr hcon)
        exact ⟨Literal.neg (.gate d),
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hd, rfl⟩), hdv⟩
    · by_cases hz : (Circuit.node true cs).eval u = true
      · exact ⟨Literal.pos (.gate d), List.mem_cons_of_mem _ List.mem_cons_self,
          (Circuit.eval_node_true_iff cs u).mp hz d hd⟩
      · exact ⟨Literal.neg (.gate (.node true cs)), List.mem_cons_self, hz⟩

/-- The canonical assignment satisfies every gate clause of `C`.

**Proof sketch.** Structural induction on the circuit.  At a leaf the encoding
contributes the two clauses expressing that the leaf's variable is equivalent to
the leaf literal; the canonical assignment gives that variable exactly the
leaf's value, so splitting on that value picks, in each of the two clauses, a
literal that holds.  At a gate the clause set is the gate's own clauses followed
by the clauses of the children: the first are covered by the preceding lemma,
the second by the induction hypothesis. -/
theorem tseitin_satisfied (u : Fin n → Bool) (C : Circuit n) :
    formulaSatisfied (tseitinAssignment u) C.tseitin := by
  have hu : ∀ i, u i = true ↔ tseitinAssignment u (CktVar.input i) := fun _ => Iff.rfl
  induction C using Circuit.ind with
  | hlit l =>
      intro c hc
      have e1 := evalLiteral_toCktLiteral_iff (α := tseitinAssignment u) hu l
      have e2 := evalLiteral_toCktLiteralNeg_iff (α := tseitinAssignment u) hu l
      have hval : tseitinAssignment u (CktVar.gate (.lit l)) ↔ l.eval u = true := by
        simp [tseitinAssignment, Circuit.eval_lit]
      simp only [Circuit.tseitin, List.mem_cons, List.not_mem_nil, or_false] at hc
      by_cases hg : l.eval u = true
      · rcases hc with rfl | rfl
        · exact ⟨l.toCktLiteral, List.mem_cons_of_mem _ List.mem_cons_self, e1.mpr hg⟩
        · exact ⟨Literal.pos (.gate (.lit l)), List.mem_cons_self, hval.mpr hg⟩
      · rcases hc with rfl | rfl
        · exact ⟨Literal.neg (.gate (.lit l)), List.mem_cons_self, fun hh => hg (hval.mp hh)⟩
        · exact ⟨l.toCktLiteralNeg, List.mem_cons_of_mem _ List.mem_cons_self, e2.mpr hg⟩
  | hnode b cs ih =>
      intro c hc
      simp only [Circuit.tseitin, List.mem_append, List.mem_flatMap] at hc
      rcases hc with hc | ⟨d, hd, hcd⟩
      · exact gateClauses_satisfied u b cs c hc
      · exact ih d hd c hcd

/-- The gate clauses of one gate pin its variable to the gate's value, given that the
children's variables are already correct.

**Proof sketch.** Split on the connective; again the two cases are dual.  Read
two facts off the clause set: from the long clause, that the gate's variable
implies the disjunction of the children's variables (OR case) or is implied by
their conjunction (AND case); and from the short clauses, one per child, the
converse implication for that child.  Unfold the gate's semantics — an OR gate
is true exactly when some child is, an AND gate exactly when all are — and each
direction of the goal is one of those two facts composed with the hypothesis
that every child's variable already agrees with that child's value. -/
theorem eval_node_iff_of_gateClauses {α : Assignment (CktVar n)} {u : Fin n → Bool}
    (b : Bool) (cs : List (Circuit n)) (hgate : formulaSatisfied α (gateClauses b cs))
    (key : ∀ c ∈ cs, (c.eval u = true ↔ α (CktVar.gate c))) :
    (Circuit.node b cs).eval u = true ↔ α (CktVar.gate (.node b cs)) := by
  cases b
  · have hmain : ¬ α (CktVar.gate (.node false cs)) ∨ ∃ c ∈ cs, α (CktVar.gate c) := by
      simpa [clauseSatisfied, evalLiteral] using
        hgate (Literal.neg (.gate (.node false cs)) :: cs.map fun c => Literal.pos (.gate c))
          List.mem_cons_self
    have hside : ∀ c ∈ cs, α (CktVar.gate (.node false cs)) ∨ ¬ α (CktVar.gate c) := by
      intro c hc
      simpa [clauseSatisfied, evalLiteral] using
        hgate [Literal.pos (.gate (.node false cs)), Literal.neg (.gate c)]
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
    rw [Circuit.eval_node_false_iff]
    constructor
    · rintro ⟨c, hc, hcv⟩
      exact (hside c hc).resolve_right (not_not_intro ((key c hc).mp hcv))
    · intro hz
      obtain ⟨c, hc, hcv⟩ := hmain.resolve_left (not_not_intro hz)
      exact ⟨c, hc, (key c hc).mpr hcv⟩
  · have hmain : α (CktVar.gate (.node true cs)) ∨ ∃ c ∈ cs, ¬ α (CktVar.gate c) := by
      simpa [clauseSatisfied, evalLiteral] using
        hgate (Literal.pos (.gate (.node true cs)) :: cs.map fun c => Literal.neg (.gate c))
          List.mem_cons_self
    have hside : ∀ c ∈ cs, ¬ α (CktVar.gate (.node true cs)) ∨ α (CktVar.gate c) := by
      intro c hc
      simpa [clauseSatisfied, evalLiteral] using
        hgate [Literal.neg (.gate (.node true cs)), Literal.pos (.gate c)]
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
    rw [Circuit.eval_node_true_iff]
    constructor
    · intro hall
      refine hmain.resolve_right ?_
      rintro ⟨c, hc, hnc⟩
      exact hnc ((key c hc).mp (hall c hc))
    · intro hz c hc
      exact (key c hc).mpr ((hside c hc).resolve_left (not_not_intro hz))

/-- Any assignment satisfying the gate clauses of `C` computes `C` correctly: the
soundness half of [AB09, Lem 6.11].

**Proof sketch.** Structural induction on the circuit.  At a leaf, the two
clauses expressing `z ↔ ℓ` give one implication each between the leaf's variable
and the leaf literal's value under the read-off input, and propositional
reasoning combines them into the equivalence.  At a gate, the clause set splits
into the gate's own clauses and the children's; the children's halves give, by
induction, that each child's variable agrees with its value, and the preceding
lemma then transfers that agreement to the gate itself. -/
theorem eval_iff_of_tseitin_satisfied {α : Assignment (CktVar n)} {u : Fin n → Bool}
    (hu : ∀ i, u i = true ↔ α (CktVar.input i)) (C : Circuit n)
    (h : formulaSatisfied α C.tseitin) :
    C.eval u = true ↔ α (CktVar.gate C) := by
  induction C using Circuit.ind with
  | hlit l =>
      have e1 := evalLiteral_toCktLiteral_iff hu l
      have e2 := evalLiteral_toCktLiteralNeg_iff hu l
      simp only [Circuit.tseitin] at h
      have h1 : ¬ α (CktVar.gate (.lit l)) ∨ l.eval u = true := by
        obtain ⟨p, hp, hv⟩ :=
          h [Literal.neg (.gate (.lit l)), l.toCktLiteral] List.mem_cons_self
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact Or.inl hv
        · exact Or.inr (e1.mp hv)
      have h2 : α (CktVar.gate (.lit l)) ∨ ¬ (l.eval u = true) := by
        obtain ⟨p, hp, hv⟩ := h [Literal.pos (.gate (.lit l)), l.toCktLiteralNeg]
          (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact Or.inl hv
        · exact Or.inr (e2.mp hv)
      rw [Circuit.eval_lit]
      tauto
  | hnode b cs ih =>
      refine eval_node_iff_of_gateClauses b cs (fun c hc => h c ?_) (fun c hc => ih c hc ?_)
      · simp only [Circuit.tseitin, List.mem_append]
        exact Or.inl hc
      · intro d hd
        refine h d ?_
        simp only [Circuit.tseitin, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨c, hc, hd⟩

/-- A circuit is satisfiable exactly when the CNF formula the reduction produces is.

**Proof sketch.** Each direction constructs the other side's witness.  From a
satisfying input, take the canonical assignment, which sets every gate variable
to that subcircuit's value: the output unit clause holds because the circuit
outputs true, and the gate clauses hold by the completeness lemma above.  From a
satisfying assignment, read an input off its values on the input variables: the
unit clause forces the output variable true, and the soundness lemma turns that
into the circuit evaluating to true on the read-off input. -/
theorem Circuit.satisfiable_iff_isSatisfiable (C : Circuit n) :
    C.Satisfiable ↔ isSatisfiable C.toCNF := by
  classical
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨tseitinAssignment u, ?_⟩
    intro c hc
    simp only [Circuit.toCNF, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨Literal.pos (.gate C), List.mem_cons_self, hu⟩
    · exact tseitin_satisfied u C c hc
  · rintro ⟨α, hα⟩
    refine ⟨fun i => if α (CktVar.input i) then true else false, ?_⟩
    have hu : ∀ i, (if α (CktVar.input i) then true else false) = true ↔
        α (CktVar.input i) := by
      intro i
      by_cases hi : α (CktVar.input i) <;> simp [hi]
    have hout : α (CktVar.gate C) := by
      simpa [clauseSatisfied, evalLiteral] using hα [Literal.pos (.gate C)] List.mem_cons_self
    exact (eval_iff_of_tseitin_satisfied hu C
      (fun c hc => hα c (List.mem_cons_of_mem _ hc))).mpr hout

/-- A circuit is satisfiable exactly when the 3-CNF formula built from its gate
clauses is.  [AB09, Lem 6.11] -/
theorem mem_cktSat_iff_is3Satisfiable (C : (n : ℕ) × Circuit n) :
    C ∈ CktSat ↔ is3Satisfiable (to3SAT C.2.toCNF) :=
  (C.2.satisfiable_iff_isSatisfiable).trans (SAT_to_3SAT_equivalence _)

/-! ## Size of the reduction -/

/-- The gate clauses of `C` number fewer than `3 * C.size`.

**Proof sketch.** Structural induction.  A leaf contributes two clauses against
a size of one.  At a gate the bound as stated is not strong enough to pass
through the children, because the gate also emits one short clause per child; the
induction therefore goes through a strengthened statement about lists, proved by
a side induction: the children's own clauses *together with one extra clause per
child* still fit inside three times the children's total size.  The gate's own
contribution is exactly one clause per child plus the long clause, and the
gate's size is one more than its children's total, so the three units of slack
the gate's own node contributes absorb the long clause; linear arithmetic
finishes. -/
theorem Circuit.tseitin_length_lt (C : Circuit n) :
    C.tseitin.length < 3 * C.size := by
  induction C using Circuit.ind with
  | hlit l => simp [Circuit.tseitin, Circuit.size]
  | hnode b cs ih =>
      have hlist : ∀ ds : List (Circuit n),
          (∀ d ∈ ds, d.tseitin.length < 3 * d.size) →
          (ds.flatMap fun d => d.tseitin).length + ds.length ≤
            3 * ds.foldr (fun d acc => d.size + acc) 0 := by
        intro ds hds
        induction ds with
        | nil => simp
        | cons d ds ihd =>
            have h1 := hds d List.mem_cons_self
            have h2 := ihd fun e he => hds e (List.mem_cons_of_mem _ he)
            simp only [List.flatMap_cons, List.length_append, List.length_cons,
              List.foldr_cons]
            omega
      have hsum := hlist cs ih
      have hg : (gateClauses b cs).length = cs.length + 1 := by
        cases b <;> simp [gateClauses]
      simp only [Circuit.tseitin, List.length_append, Circuit.size, hg]
      omega

/-- The reduction produces at most `3 * C.size` clauses. -/
theorem Circuit.toCNF_length_le (C : Circuit n) : C.toCNF.length ≤ 3 * C.size := by
  have h := C.tseitin_length_lt
  simp only [Circuit.toCNF, List.length_cons]
  omega

end BoolCircuit
