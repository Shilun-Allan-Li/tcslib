<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.clauseToTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An AND-clause read as a DNF term

**Definition.** `NAndCircuit.clauseToTerm : NAndCircuit n → Term n` sends

- `.clause lits _` to `lits.map Lit.toLiteral`, the same literals converted from
  the `Lit` representation (`sign : Bool`, `true` = positive) to the
  switching-lemma `Literal` representation (`neg = !sign`);
- `.node _` to the empty term `[]`.

The `Nodup` proof carried by `.clause` is discarded here; it is re-exposed
separately by `NAndCircuit.clauseToTerm_nodup`.

**Remark.** The `.node` case is a junk value, not a mathematical claim: the
function is only ever applied to the clause children of a depth-2 node, and
`[]` is the term that evaluates to `true` under `Term.eval`, so the fallback is
never exercised in the correctness lemmas.

**Used in.** `NOrCircuit.toDNF` (mapping it over the AND-children of an OR node),
and hence in `NOrCircuit.node_eval_eq_toDNF_eval`,
`NAndCircuit.clauseToTerm_nodup`, `NAndCircuit.clauseToTerm_var_inj`,
`NAndCircuit.clauseToTerm_width`, and `NOrCircuit.toDNF_width_bounded`.
