<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.clauseToTerm_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width of a converted OR-clause is its literal count

**Claim.** For `lits : List (Lit n)` with `(lits.map Lit.idx).Nodup`,
`Term.width (NOrCircuit.clause lits h).clauseToTerm = lits.length`.

**Proof.** Immediate from `simp [NOrCircuit.clauseToTerm, Term.width]`:
unfolding gives `(lits.map Lit.toLiteral).length`, and `List.length_map`
(applied by `simp`) reduces it to `lits.length`.

**Remark.** `Term.width` is by definition `List.length`, so the statement is a
bookkeeping bridge between the circuit-side literal list and the
switching-lemma-side width measure. `NAndCircuit.clauseToTerm_width` is the
identical statement for AND-clauses.
