<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: cleanCNF_D3_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a CNF preserves its value

**Claim.** For every `ψ : CNF n` and every `x : Fin n → Bool`,
`CNF.eval (cleanCNF_D3 ψ) x = CNF.eval ψ x`, where
`cleanCNF_D3 ψ = (ψ.filter (fun c => ¬clauseIsTaut c)).map dedupClauseVars`
deletes tautological clauses and then removes repeated variables inside each
surviving clause.

**Proof.**

1. `unfold cleanCNF_D3` and `unfold CNF.eval`; since `CNF.eval` is
   `List.all` of `CNF.evalClause`, push the `map` through with
   `simp +decide [List.all_map]`, reducing the goal to a clause-by-clause
   comparison over `ψ` (`congr! 2 with t ht`).
2. Split on `by_cases h : clauseIsTaut t`.
3. Tautological `t`: it is dropped by the filter, and
   `clauseIsTaut_eval_true t h x` says it evaluated to `true` anyway, so the
   conjunction is unchanged (`aesop`).
4. Non-tautological `t`: it is kept, in deduplicated form, and
   `dedupClauseVars_eval_of_not_taut t h x` says the deduplicated clause has the
   same value.

**Anomaly.** Step 4 rests on `dedupClauseVars_eval_of_not_taut`, whose Lean body
is `sorry`, so this lemma is currently proved only modulo that gap.

**Used in.** `exists_nice_cnf_of_cnf` (with `cleanCNF_D3_width_le`,
`cleanCNF_D3_nodup`, `cleanCNF_D3_var_inj`), which supplies the "nice CNF"
normal form the switching lemma consumes.
