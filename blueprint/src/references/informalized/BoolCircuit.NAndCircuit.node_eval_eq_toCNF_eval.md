<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.node_eval_eq_toCNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A depth-2 AND-of-ORs evaluates as its CNF

**Claim.** Let `cs : List (NOrCircuit n)` in which every child is a clause,
`h_clauses : ∀ c ∈ cs, ∃ lits h, c = NOrCircuit.clause lits h`. Then for every
input `x`, `(NAndCircuit.node cs).eval x = CNF.eval (NAndCircuit.node cs).toCNF x`.
So the semantic bridge from the normal-form circuit type to the switching-lemma
`CNF` type is exact, provided the node really is depth 2.

**Proof.** `induction cs <;> simp_all +decide [NAndCircuit.eval]`, then the two
cases.

1. Empty list: the AND-fold is `true` and `CNF.eval [] x = [].all _` is also
   `true`; `exact rfl`.
2. Cons: `rename_i` names the head, the tail list and the induction hypothesis;
   `rcases h_clauses.1 with ⟨lits, h, rfl⟩` replaces the head by
   `NOrCircuit.clause lits h` (`simp_all` has already split the cons form of
   `h_clauses` into head and tail parts), and
   `simp_all [NOrCircuit.eval, NAndCircuit.toCNF]` plus
   `simp [CNF.eval, NOrCircuit.clauseToTerm]` exposes both sides as
   `head && tail`.
3. The head factors agree by `foldr_or_lits_eq_clause_eval lits x`: the OR-fold
   of the source literals equals `CNF.evalClause (lits.map Lit.toLiteral) x`.
   `convert congr_arg (fun y => y && …) … using 1` conjoins that equality with
   the tail factor supplied by the induction hypothesis.

**Used in.** Nothing yet — it is the CNF-side counterpart of
`NOrCircuit.node_eval_eq_toDNF_eval`, kept so the AND/OR duality of this file is
complete.
