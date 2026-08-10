<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: clauseIsTaut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tautological clause

**Definition.** For a clause `c : List (Literal n)` (read as a disjunction of
literals), `clauseIsTaut c : Prop` says that `c` contains two literals on the
same variable with opposite polarities:

`∃ l₁ ∈ c, ∃ l₂ ∈ c, l₁.var = l₂.var ∧ l₁.neg ≠ l₂.neg`.

Such a clause contains both `x i` and `¬x i`, hence evaluates to `true` on every
input — that is exactly `clauseIsTaut_eval_true`. The definition is accompanied by
a `Decidable` instance obtained by `unfold clauseIsTaut; infer_instance`
(decidability of a bounded double existential over a list with `DecidableEq`
literals), which is what lets tautological clauses be `List.filter`ed out.

**Remark.** This is the disjunctive dual of `termHasContradiction` in
`CircuitHelpers.lean`: for a *term* (conjunction) the same syntactic pattern makes
the term unsatisfiable, for a *clause* it makes it valid.

**Used in.** `dedupClauseVars_eval_of_not_taut`, `cleanCNF_D3` (as the filter
predicate), and `cleanCNF_D3_eval`.
