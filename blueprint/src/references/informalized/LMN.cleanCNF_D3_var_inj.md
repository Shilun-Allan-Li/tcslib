<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: cleanCNF_D3_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every clause of a cleaned CNF is variable-injective

**Claim.** For every `ψ : CNF n`, every clause `c ∈ cleanCNF_D3 ψ` and all
`l₁, l₂ ∈ c` with `l₁.var = l₂.var`, we have `l₁ = l₂`. That is, no variable
occurs twice in a cleaned clause.

**Proof.**

1. `intros c hc l₁ hl₁ l₂ hl₂ hvar`, then `apply dedupClauseVars_var_inj`; the
   equal-variable hypothesis is discharged by `assumption`.
2. Two membership side goals remain: `l₁` and `l₂` must lie in
   `dedupClauseVars c'` for the pre-image clause `c'`. Both are settled by
   `unfold cleanCNF_D3 at hc; unfold dedupClauseVars at *; aesop`, which uses
   `hc` to identify `c` with `dedupClauseVars c'` for some `c'` in the filtered
   list.

**Used in.** `exists_nice_cnf_of_cnf`; together with `cleanCNF_D3_nodup` these are
the two per-clause hygiene conditions in the switching lemma's "nice CNF"
interface.
