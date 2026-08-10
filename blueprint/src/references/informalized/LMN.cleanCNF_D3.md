<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: cleanCNF_D3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a CNF for the switching-lemma hypotheses

**Definition.** For `ψ : CNF n`, `cleanCNF_D3 ψ` deletes the tautological clauses
and then deduplicates variables inside each surviving clause:

`(ψ.filter (fun c => ¬clauseIsTaut c)).map dedupClauseVars`.

The four properties proved about it are exactly the interface the CNF switching
lemma needs:

- `cleanCNF_D3_eval` — evaluation is unchanged, `CNF.eval (cleanCNF_D3 ψ) x = CNF.eval ψ x`
  (deleted clauses were `true` anyway by `clauseIsTaut_eval_true`; surviving ones
  are preserved by `dedupClauseVars_eval_of_not_taut`);
- `cleanCNF_D3_width_le` — `CNF.width (cleanCNF_D3 ψ) ≤ CNF.width ψ`, from
  `dedupClauseVars_length_le`;
- `cleanCNF_D3_nodup` and `cleanCNF_D3_var_inj` — every clause is `Nodup` and
  variable-injective.

**Remark.** It duplicates `cleanCNF` of `CircuitHelpers.lean` (same
filter-then-dedup shape, built on `clauseIsTaut`/`dedupClauseVars` rather than
`termHasContradiction`/`dedupTermVar`); the `_D3` suffix marks the local copy used
by the depth-3 argument.

**Used in.** `depth3_second_stage_bound`, to turn the CNF produced by stage 1 into
one satisfying the hypotheses of `switching_bernoulli_dtDepth_cnf`.
