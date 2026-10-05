import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.CircuitComplexity.Formulas

/-!
# Conversions between Normal-Form Circuits and DNF/CNF

This file provides conversions between the `NAndCircuit`/`NOrCircuit` normal-form
circuit types and the `DNF`/`CNF` types used in the switching lemma.

## Literal conversion

`BoolCircuit.Lit` uses `sign : Bool` where `true` = positive literal.
`Literal` uses `neg : Bool` where `true` = negated literal.

## Depth-2 normal-form circuits as DNF/CNF

A depth-2 `NOrCircuit.node [NAndCircuit.clause ...]` evaluates as a DNF:
  OR(AND(lits₁), AND(lits₂), ...) = disjunction of conjunctions.

A depth-2 `NAndCircuit.node [NOrCircuit.clause ...]` evaluates as a CNF:
  AND(OR(lits₁), OR(lits₂), ...) = conjunction of disjunctions.
-/

set_option maxHeartbeats 800000

/-! ## Literal Conversions -/

/-- Convert a `BoolCircuit.Lit` to a switching-lemma `Literal`. -/
def BoolCircuit.Lit.toLiteral {n : ℕ} (l : BoolCircuit.Lit n) : Literal n :=
  ⟨l.idx, !l.sign⟩

/-- Evaluation of a converted literal agrees. -/
theorem BoolCircuit.Lit.eval_eq_toLiteral_eval {n : ℕ} (l : BoolCircuit.Lit n)
    (x : Fin n → Bool) :
    l.eval x = l.toLiteral.eval x := by
  simp [BoolCircuit.Lit.eval, Literal.eval, BoolCircuit.Lit.toLiteral]
  cases l.sign <;> simp

namespace BoolCircuit

/-! ## Converting clauses to terms and clauses -/

/-- Convert an AND-clause's literals to a `Term` (conjunction of literals). -/
def NAndCircuit.clauseToTerm : NAndCircuit n → Term n
  | .clause lits _ => lits.map Lit.toLiteral
  | .node _ => []

/-- Convert an OR-clause's literals to a `Clause` (disjunction of literals). -/
def NOrCircuit.clauseToClause : NOrCircuit n → Clause n
  | .clause lits _ => lits.map Lit.toLiteral
  | .node _ => []

/-- Convert a depth-2 NOrCircuit (= OR of AND-clauses) to a DNF. -/
def NOrCircuit.toDNF : NOrCircuit n → DNF n
  | .clause _ _ => ⟨[]⟩
  | .node cs => ⟨cs.map NAndCircuit.clauseToTerm⟩

/-- Convert a depth-2 NAndCircuit (= AND of OR-clauses) to a CNF. -/
def NAndCircuit.toCNF : NAndCircuit n → CNF n
  | .clause _ _ => ⟨[]⟩
  | .node cs => ⟨cs.map NOrCircuit.clauseToClause⟩

/-! ## Evaluation preservation -/

/-
Conjunction of Lits evaluates like a Term of converted Literals.
-/
theorem foldr_and_lits_eq_term_eval (lits : List (Lit n)) (x : Fin n → Bool) :
    lits.foldr (fun l acc => l.eval x && acc) true =
    Term.eval (lits.map Lit.toLiteral) x := by
  induction lits <;> simp_all +decide [ Term.eval ];
  unfold BoolCircuit.Lit.toLiteral; aesop;

/-
Disjunction of Lits evaluates like a CNF clause of converted Literals.
-/
theorem foldr_or_lits_eq_clause_eval (lits : List (Lit n)) (x : Fin n → Bool) :
    lits.foldr (fun l acc => l.eval x || acc) false =
    Clause.eval (lits.map Lit.toLiteral) x := by
  unfold Clause.eval;
  induction lits <;> simp +decide [*];
  unfold BoolCircuit.Lit.toLiteral; aesop;

/-
A NOrCircuit.node of NAndCircuit.clauses evaluates as the corresponding DNF.
-/
theorem NOrCircuit.node_eval_eq_toDNF_eval
    (cs : List (NAndCircuit n)) (x : Fin n → Bool)
    (h_clauses : ∀ c ∈ cs, ∃ lits h, c = NAndCircuit.clause lits h) :
    (NOrCircuit.node cs).eval x = DNF.eval (NOrCircuit.node cs).toDNF x := by
  -- By induction on `cs`, we can show that the evaluation of the NOrCircuit.node is equal to the evaluation of the DNF.
  induction' cs with c cs ih;
  · unfold NOrCircuit.eval NOrCircuit.toDNF; simp +decide ;
  · simp_all +decide [ NOrCircuit.eval, NOrCircuit.toDNF ];
    rcases h_clauses.1 with ⟨ lits, h, rfl ⟩ ; simp +decide [ NAndCircuit.clauseToTerm ] ;
    rw [ ← foldr_and_lits_eq_term_eval ];
    unfold NAndCircuit.eval; aesop;

/-
A NAndCircuit.node of NOrCircuit.clauses evaluates as the corresponding CNF.
-/
theorem NAndCircuit.node_eval_eq_toCNF_eval
    (cs : List (NOrCircuit n)) (x : Fin n → Bool)
    (h_clauses : ∀ c ∈ cs, ∃ lits h, c = NOrCircuit.clause lits h) :
    (NAndCircuit.node cs).eval x = CNF.eval (NAndCircuit.node cs).toCNF x := by
  induction cs <;> simp_all +decide [ NAndCircuit.eval ];
  · exact rfl;
  · rename_i k hk ih; rcases h_clauses.1 with ⟨ lits, h, rfl ⟩ ; simp_all +decide [NOrCircuit.eval, NAndCircuit.toCNF] ;
    simp +decide [ NOrCircuit.clauseToClause ];
    convert congr_arg ( fun y => y && hk.all ( ( fun t => Clause.eval t x ) ∘ NOrCircuit.clauseToClause ) ) ( foldr_or_lits_eq_clause_eval lits x ) using 1

/-! ## Nodup / injectivity for switching lemma compatibility -/

/-
A converted clause from `NAndCircuit.clause` preserves Nodup.
-/
theorem NAndCircuit.clauseToTerm_nodup (lits : List (Lit n))
    (h : (lits.map Lit.idx).Nodup) :
    (NAndCircuit.clause lits h).clauseToTerm.Nodup := by
  unfold NAndCircuit.clauseToTerm;
  convert h using 1;
  constructor <;> intro h <;> rw [ List.nodup_iff_injective_get ] at *;
  · grind;
  · intro i j hij; have := @h ⟨ i, by
      exact i.2.trans_le ( by simp ) ⟩ ⟨ j, by
      exact j.2.trans_le ( by simp ) ⟩ ; simp_all +decide ;
    exact Fin.ext ( this ( by injection hij ) )

/-
Variable-index injectivity in a converted clause.
-/
theorem NAndCircuit.clauseToTerm_var_inj (lits : List (Lit n))
    (h : (lits.map Lit.idx).Nodup) :
    ∀ l₁ ∈ (NAndCircuit.clause lits h).clauseToTerm,
    ∀ l₂ ∈ (NAndCircuit.clause lits h).clauseToTerm,
    l₁.var = l₂.var → l₁ = l₂ := by
  -- By definition of `clauseToTerm`, if `l₁` and `l₂` are in the list `lits.map toLiteral`, then they are in the list `lits`.
  simp [NAndCircuit.clauseToTerm];
  unfold BoolCircuit.Lit.toLiteral;
  intro a h_1 a_1 h_2 h_3
  have ha_eq : a = a_1 := by
    by_contra ha_ne
    exact absurd h_3 ((List.pairwise_map.mp h).forall (fun _ _ hh => hh.symm) h_1 h_2 ha_ne)
  rw [ha_eq]

/-
A converted clause from `NOrCircuit.clause` preserves Nodup.
-/
theorem NOrCircuit.clauseToClause_nodup (lits : List (Lit n))
    (h : (lits.map Lit.idx).Nodup) :
    (NOrCircuit.clause lits h).clauseToClause.Nodup := by
  convert NAndCircuit.clauseToTerm_nodup lits h using 1

/-
Variable-index injectivity in a converted OR-clause.
-/
theorem NOrCircuit.clauseToClause_var_inj (lits : List (Lit n))
    (h : (lits.map Lit.idx).Nodup) :
    ∀ l₁ ∈ (NOrCircuit.clause lits h).clauseToClause,
    ∀ l₂ ∈ (NOrCircuit.clause lits h).clauseToClause,
    l₁.var = l₂.var → l₁ = l₂ := by
  convert NAndCircuit.clauseToTerm_var_inj lits h using 1

/-! ## Width bounds -/

/-- Width of a converted clause equals the number of literals. -/
theorem NAndCircuit.clauseToTerm_width (lits : List (Lit n))
    (h : (lits.map Lit.idx).Nodup) :
    LitList.width (NAndCircuit.clause lits h).clauseToTerm = lits.length := by
  simp [NAndCircuit.clauseToTerm, LitList.width]

theorem NOrCircuit.clauseToClause_width (lits : List (Lit n))
    (h : (lits.map Lit.idx).Nodup) :
    LitList.width (NOrCircuit.clause lits h).clauseToClause = lits.length := by
  simp [NOrCircuit.clauseToClause, LitList.width]

/-
Width of a DNF from a NOrCircuit.node is bounded by the max clause size.
-/
theorem NOrCircuit.toDNF_width_bounded (cs : List (NAndCircuit n)) (w : ℕ)
    (h_clauses : ∀ c ∈ cs, ∃ (lits : List (Lit n)) (h : (lits.map Lit.idx).Nodup),
      c = NAndCircuit.clause lits h ∧ lits.length ≤ w) :
    DNF.width (NOrCircuit.node cs).toDNF ≤ w := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    obtain ⟨lits, h, rfl, hl⟩ := h_clauses c (by simp)
    have ih' := ih (fun c hc => h_clauses c (by simp [hc]))
    simp only [NOrCircuit.toDNF, DNF.width_mk, Depth2.width, List.map_cons,
      List.foldr_cons] at ih' ⊢
    exact max_le (NAndCircuit.clauseToTerm_width lits h ▸ hl) ih'

/-
Width of a CNF from a NAndCircuit.node is bounded by the max clause size.
-/
theorem NAndCircuit.toCNF_width_bounded (cs : List (NOrCircuit n)) (w : ℕ)
    (h_clauses : ∀ c ∈ cs, ∃ (lits : List (Lit n)) (h : (lits.map Lit.idx).Nodup),
      c = NOrCircuit.clause lits h ∧ lits.length ≤ w) :
    CNF.width (NAndCircuit.node cs).toCNF ≤ w := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    obtain ⟨lits, h, rfl, hl⟩ := h_clauses c (by simp)
    have ih' := ih (fun c hc => h_clauses c (by simp [hc]))
    simp only [NAndCircuit.toCNF, CNF.width_mk, Depth2.width, List.map_cons,
      List.foldr_cons] at ih' ⊢
    exact max_le (NOrCircuit.clauseToClause_width lits h ▸ hl) ih'

/-! ## DNF properties for depth-2 NOrCircuit -/

/-
The DNF from a depth-2 NOrCircuit satisfies the Nodup condition
    required by the switching lemma.
-/
theorem NOrCircuit.toDNF_terms_nodup (cs : List (NAndCircuit n))
    (h_clauses : ∀ c ∈ cs, ∃ (lits : List (Lit n)) (h : (lits.map Lit.idx).Nodup),
      c = NAndCircuit.clause lits h) :
    ∀ t ∈ (NOrCircuit.node cs).toDNF.terms, t.Nodup := by
  intro t ht; obtain ⟨ c, hc, rfl ⟩ := List.mem_map.mp ht; obtain ⟨ lits, h, rfl ⟩ := h_clauses c hc; exact NAndCircuit.clauseToTerm_nodup lits h;

/-
The DNF from a depth-2 NOrCircuit satisfies the variable-injectivity
    condition required by the switching lemma.
-/
theorem NOrCircuit.toDNF_var_inj (cs : List (NAndCircuit n))
    (h_clauses : ∀ c ∈ cs, ∃ (lits : List (Lit n)) (h : (lits.map Lit.idx).Nodup),
      c = NAndCircuit.clause lits h) :
    ∀ t ∈ (NOrCircuit.node cs).toDNF.terms,
      ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂ := by
  intro t ht l₁ hl₁ l₂ hl₂ hvar
  obtain ⟨c, hc, rfl⟩ : ∃ c ∈ cs, t = c.clauseToTerm := by
    unfold NOrCircuit.toDNF at ht; aesop;
  obtain ⟨ lits, h, rfl ⟩ := h_clauses c hc; exact NAndCircuit.clauseToTerm_var_inj lits h l₁ hl₁ l₂ hl₂ hvar;

/-
The CNF from a depth-2 NAndCircuit satisfies the Nodup condition.
-/
theorem NAndCircuit.toCNF_clauses_nodup (cs : List (NOrCircuit n))
    (h_clauses : ∀ c ∈ cs, ∃ (lits : List (Lit n)) (h : (lits.map Lit.idx).Nodup),
      c = NOrCircuit.clause lits h) :
    ∀ c ∈ (NAndCircuit.node cs).toCNF.clauses, c.Nodup := by
  intros t ht; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht; obtain ⟨lits, h, rfl⟩ := h_clauses c hc; exact NOrCircuit.clauseToClause_nodup lits h;

/-
The CNF from a depth-2 NAndCircuit satisfies the variable-injectivity.
-/
theorem NAndCircuit.toCNF_var_inj (cs : List (NOrCircuit n))
    (h_clauses : ∀ c ∈ cs, ∃ (lits : List (Lit n)) (h : (lits.map Lit.idx).Nodup),
      c = NOrCircuit.clause lits h) :
    ∀ c ∈ (NAndCircuit.node cs).toCNF.clauses,
      ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂ := by
  intros t ht l₁ hl₁ l₂ hl₂ hvar
  obtain ⟨c, hc⟩ : ∃ c ∈ cs, t = NOrCircuit.clauseToClause c := by
    unfold NAndCircuit.toCNF at ht; aesop;
  rcases h_clauses c hc.1 with ⟨ lits, h, rfl ⟩ ; exact NOrCircuit.clauseToClause_var_inj lits h _ ( by aesop ) _ ( by aesop ) hvar;

end BoolCircuit