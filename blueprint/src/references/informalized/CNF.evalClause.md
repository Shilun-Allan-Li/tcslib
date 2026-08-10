<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: CNF.evalClause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluation of a single CNF clause

**Definition.** For a clause `t : Term n` and an assignment `x : Fin n → Bool`,

`CNF.evalClause t x = t.any (fun l => l.eval x)`,

i.e. the clause is true exactly when *some* literal in it is satisfied by `x`
(each literal evaluated by `Literal.eval`).

Being a `List.any`, the empty clause evaluates to `false`.

**Remark.** The argument type is `Term n`, the same list-of-literals type that
`Term.eval` reads conjunctively; `CNF.evalClause` is precisely the disjunctive
re-reading of that data, which is why CNF clauses need this separate evaluator
rather than reusing `Term.eval`.

**Used in.** `CNF.eval`, which conjoins `CNF.evalClause` over all clauses; and
via that in `TCSlib/BooleanAnalysis/Switching.lean` and
`LMN/NormalFormConversion.lean`, where it is typically unfolded by
`simp [CNF.eval]`.
