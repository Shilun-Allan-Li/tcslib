<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: dedupClauseVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deduplicating the variables of a clause

**Definition.** `dedupClauseVars c : List (Literal n)` keeps, for each variable
index, only the first literal of `c` mentioning it:

`c.pwFilter (fun l₁ l₂ => decide (l₁.var ≠ l₂.var))`.

`List.pwFilter R` retains an element only if it is `R`-related to all elements
already kept, so the result is a sublist of `c` whose literals have pairwise
distinct `var` fields.

Its three recorded consequences are: `dedupClauseVars_var_inj` (two kept literals
with equal `var` are equal), `dedupClauseVars_nodup` (the result has no
duplicates, from `List.pairwise_pwFilter`), and `dedupClauseVars_length_le` (via
`List.pwFilter_sublist`, so `Term.width` does not increase).

**Remark.** The switching lemma hypotheses `hnd`/`hnodup` of
`switching_bernoulli_dtDepth_cnf` demand precisely variable-injectivity and
nodup-ness per clause; `dedupClauseVars` is the normalizer that manufactures
them, and it is sound on clauses that are not tautological
(`dedupClauseVars_eval_of_not_taut`).

**Used in.** `cleanCNF_D3`.
