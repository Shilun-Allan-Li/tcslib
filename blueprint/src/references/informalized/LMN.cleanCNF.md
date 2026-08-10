<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a CNF for the switching-lemma hypotheses

**Definition.** For `c : CNF n`,

`cleanCNF c = (c.filter (fun t => !termHasContradiction t)).map dedupTermVar`

— literally the same expression as `cleanDNF`, since `CNF n` and `DNF n` are both
abbreviations for `List (Term n)`; only the intended reading changes. A clause
containing a variable in both polarities is a **tautology**, so deleting it does
not change the conjunction, and `dedupTermVar` then makes each surviving clause
variable-injective.

The accompanying lemmas mirror the DNF ones:

- `cleanCNF_eval` — `CNF.eval (cleanCNF c) x = CNF.eval c x`, using
  `contradiction_clause_eval_true` for the deleted clauses and
  `dedupTermVar_preserves_clause_eval` for the kept ones;
- `cleanCNF_width_le` — `CNF.width (cleanCNF c) ≤ CNF.width c`, from
  `dedupTermVar_width_le` and a `foldr max` monotonicity induction;
- `cleanCNF_var_inj`, `cleanCNF_nodup` — from `dedupTermVar_var_inj` /
  `dedupTermVar_nodup` after `List.mem_map`.

**Remark.** Same filter for both normal forms, opposite reasons: a contradictory
term is `false` and is dropped from a disjunction; a contradictory clause is
`true` and is dropped from a conjunction. `LMN/Depth3Switching.lean` carries a
near-duplicate, `cleanCNF_D3`, built on `clauseIsTaut`/`dedupClauseVars`.

**Used in.** `switching_bernoulli_dtDepth_cnf_general` (same file), which uses it
to discharge the `var_inj`/`Nodup` hypotheses of
`switching_bernoulli_dtDepth_cnf` for an arbitrary CNF.
