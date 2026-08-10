<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.node_eval_eq_toDNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A depth-2 OR-circuit evaluates as its DNF

**Claim.** Let `cs : List (NAndCircuit n)` with every `c ∈ cs` of clause form
`NAndCircuit.clause lits h`, and let `x : Fin n → Bool`. Then
`(NOrCircuit.node cs).eval x = DNF.eval (NOrCircuit.node cs).toDNF x`, i.e.
the OR-of-AND-clauses circuit and the DNF `cs.map NAndCircuit.clauseToTerm`
agree pointwise.

**Proof.** Induction on `cs` (`induction' cs with c cs ih`).

- **Base.** `unfold NOrCircuit.eval NOrCircuit.toDNF; simp +decide` reduces
  both sides to the empty disjunction; `rfl` finishes (`foldr … false = false`
  and `DNF.eval [] x = false`).
- **Step.** `simp_all +decide [NOrCircuit.eval, NOrCircuit.toDNF]` splits both
  sides into head-`or`-tail, the tail matching `ih` (whose clause hypothesis
  comes from `h_clauses` restricted to the tail).
  1. `rcases h_clauses.1` writes the head as `NAndCircuit.clause lits h`.
  2. `simp +decide [NAndCircuit.clauseToTerm, DNF.eval]` exposes the head term
     as `Term.eval (lits.map Lit.toLiteral) x`.
  3. `rw [← foldr_and_lits_eq_term_eval]` turns that term evaluation back into
     the literal-wise conjunction `lits.foldr (fun l acc => l.eval x && acc) true`
     — the bridge lemma carrying `Lit.eval_eq_toLiteral_eval`.
  4. `unfold NAndCircuit.eval; aesop` matches it with the clause's own
     evaluation.

**Used in.** The semantic half of the normal-form ↔ DNF/CNF interface;
`NAndCircuit.node_eval_eq_toCNF_eval` is the dual statement for CNF.
