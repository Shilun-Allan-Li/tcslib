<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: contradiction_clause_eval_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A clause containing a variable and its negation is a tautology

**Claim.** If `termHasContradiction t = true` then `CNF.evalClause t x = true`
for every `x : Fin n → Bool`. The same list `t` that is a contradictory
*conjunction* is a tautological *disjunction*, `CNF.evalClause` being the OR
(`List.any`) of the literals.

**Proof.** Essentially one automation step. Unfold `termHasContradiction` in
`hc` and unfold `CNF.evalClause`, then `simp_all +decide [Literal.eval]`
followed by `grind`: the hypothesis names two literals of `t` on a common
variable `v` with opposite polarities, so whichever value `x v` takes, one of
them evaluates to `true`, and one true disjunct suffices.

**Used in.** `cleanCNF_eval` — it justifies dropping tautological clauses from
a CNF, a true conjunct being redundant. Dual to
`contradiction_term_eval_false`.
