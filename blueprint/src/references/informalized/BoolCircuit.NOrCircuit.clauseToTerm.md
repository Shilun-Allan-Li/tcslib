<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.clauseToTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An OR-clause read as a CNF clause

**Definition.** `NOrCircuit.clauseToTerm : NOrCircuit n → Term n` sends

- `.clause lits _` to `lits.map Lit.toLiteral` (indices kept, `neg = !sign`);
- `.node _` to `[]`.

Its body is identical to `NAndCircuit.clauseToTerm`; only the input type differs.
Since `CNF n` is also `List (Term n)`, the resulting list of literals is meant to
be read disjunctively, via `CNF.evalClause`, rather than as a conjunction.

**Remark.** The reuse of `Term n` for both DNF terms and CNF clauses is why the
two functions look the same — the AND/OR reading lives in the evaluator
(`Term.eval` versus `CNF.evalClause`), not in the data.

**Used in.** `NAndCircuit.toCNF` (mapping it over the OR-children of an AND
node), and hence in `NAndCircuit.node_eval_eq_toCNF_eval`,
`NOrCircuit.clauseToTerm_nodup`, `NOrCircuit.clauseToTerm_var_inj`,
`NOrCircuit.clauseToTerm_width`, and `NAndCircuit.toCNF_width_bounded`.
