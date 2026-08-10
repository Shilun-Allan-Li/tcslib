<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: dedupClauseVars_eval_of_not_taut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deduplication preserves the value of a non-tautological clause

**Claim.** Let `c : List (Literal n)` be a clause that is *not* tautological
(`¬clauseIsTaut c`, so no variable occurs in `c` with both polarities). Then for
every assignment `x : Fin n → Bool`,
`(dedupClauseVars c).any (fun l => l.eval x) = c.any (fun l => l.eval x)`.

**Proof.** **Not yet proved — the Lean body is `sorry`.** The source carries the
comment "grind failures in pwFilter induction; needs interactive debugging".

The intended argument: `dedupClauseVars c` drops a literal `l` only when an
earlier literal on the same variable `l.var` was kept. Non-tautology forces the
two to have the *same* polarity, hence to be the same literal (`Literal` is a
`var`/`neg` pair), so the dropped literal contributes nothing new to the
disjunction; `List.pwFilter_sublist` gives `≤` and this observation gives `≥`.

**Used in.** `cleanCNF_D3_eval`, and therefore transitively in
`exists_nice_cnf_of_cnf`, `dtDepth_le_implies_nice_cnf`,
`switching_bernoulli_dtDepth_function`, `depth3_second_stage_bound` and
`depth3_switching_bound` — this `sorry` is the single open gap under the
depth-3 switching chain in this file.
