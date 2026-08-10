<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanCNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a CNF preserves its value

**Claim.** For every `c : CNF n` and every `x : Fin n → Bool`,
`CNF.eval (cleanCNF c) x = CNF.eval c x`, where
`cleanCNF c = (c.filter (fun t => !termHasContradiction t)).map dedupTermVar`
deletes the clauses containing a variable in both polarities and then removes
repeated variables from each surviving clause.

**Proof.** `unfold cleanCNF CNF.eval`, then
`induction' c with t c ih <;> simp +decide [*]`.

1. Empty CNF: closed by the `simp` (both sides are `true`).
2. Cons `t :: c`: `by_cases h : termHasContradiction t`, then
   `simp +decide [h, contradiction_clause_eval_true, dedupTermVar_preserves_clause_eval]`
   in each branch.
3. Clause dropped: `contradiction_clause_eval_true t x h` says such a clause has
   `CNF.evalClause t x = true`, so removing it from the `List.all` conjunction
   changes nothing; `grind` finishes.
4. Clause kept: `dedupTermVar_preserves_clause_eval t x h` says the deduplicated
   clause has the same `CNF.evalClause` value; `grind` finishes.

One remark: `cleanCNF` and `cleanDNF` are the *same* function (`CNF n` and
`DNF n` are both `List (Term n)`), and `termHasContradiction` is the same test;
what differs is why dropping is sound — such a clause is a tautology (`true`
under `∧`) whereas such a term is contradictory (`false` under `∨`).

**Used in.** `switching_bernoulli_dtDepth_cnf_general`, which is the only caller.
