<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: termHasContradiction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A term containing a variable and its negation

**Definition.** `termHasContradiction t` is the `Bool`-valued test, on a term
`t : Term n` (a list of literals), given by the doubly-nested `List.any`

```
t.any (fun l₁ => t.any (fun l₂ => decide (l₁.var = l₂.var) && decide (l₁.neg ≠ l₂.neg)))
```

so it is `true` exactly when `t` contains two literals on the same variable with
opposite signs. Note it is `Bool`, not `Prop`; call sites use it under
`by_cases`/`simp +decide` and negate it as `!termHasContradiction t`.

Because a term is read conjunctively and a clause disjunctively, the flag means
opposite things on the two sides, and both are proved in the same file:
`contradiction_term_eval_false` (the term evaluates to `false` everywhere) and
`contradiction_clause_eval_true` (the clause evaluates to `true` everywhere).

**Used in.** `cleanDNF` and `cleanCNF`, which first
`filter (fun t => !termHasContradiction t)` to drop the trivially-false terms
(resp. trivially-true clauses) and then `map dedupTermVar` over what survives.
The evaluation-preservation and width-bound lemmas for those two cleaners
(`dedupTermVar_preserves_term_eval`, `dedupTermVar_preserves_clause_eval`, and
the `foldr max` width arguments) all case-split on this flag.
