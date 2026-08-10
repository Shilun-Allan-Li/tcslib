<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.clauseToTerm_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Variable-injectivity of a converted OR-clause

**Claim.** Let `lits : List (Lit n)` with `(lits.map Lit.idx).Nodup`. In the
`Term` obtained by `(NOrCircuit.clause lits h).clauseToTerm` (i.e.
`lits.map Lit.toLiteral`), any two literals with the same variable are equal:
`∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂`.

**Proof.** One line: `convert NAndCircuit.clauseToTerm_var_inj lits h using 1`.

- `NOrCircuit.clauseToTerm` and `NAndCircuit.clauseToTerm` both unfold to
  `lits.map Lit.toLiteral` on the `clause` constructor, so the two statements
  are equal up to that definitional step, which `convert … using 1` discharges.

**Remark.** The AND/OR distinction is only about how the clause is *evaluated*
(conjunction vs. disjunction); the literal list, and hence this
injectivity property, is the same, so the OR case is not proved independently.
