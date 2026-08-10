<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.clauseToTerm_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Converting an AND-clause preserves `Nodup`

**Claim.** If `lits : List (Lit n)` has distinct variable indices,
`h : (lits.map Lit.idx).Nodup`, then the term produced by
`(NAndCircuit.clause lits h).clauseToTerm` is duplicate-free as a list of
`Literal n`. Since `clauseToTerm` on a clause is just `lits.map Lit.toLiteral`
with `Lit.toLiteral ⟨i, s⟩ = ⟨i, !s⟩`, this says: index-distinctness of the
source literals gives literal-distinctness of the converted term.

**Proof.**

1. `unfold NAndCircuit.clauseToTerm` puts the goal in the form
   `(lits.map Lit.toLiteral).Nodup`.
2. `convert h using 1` reduces it to the equivalence
   `(lits.map Lit.toLiteral).Nodup ↔ (lits.map Lit.idx).Nodup`, and
   `constructor <;> intro h <;> rw [List.nodup_iff_injective_get] at *`
   restates both directions as injectivity of `List.get`.
3. One direction is vacuous: after `intro h` shadows the name, the goal *is* the
   ambient hypothesis, and `grind` closes it by assumption — no content there.
4. The substantive direction instantiates the index-injectivity at the two
   positions, transporting the `Fin` bounds across `List.length_map`
   (`i.2.trans_le (by simp)`); `injection hij` extracts equality of the `var`
   fields of the converted literals, i.e. equality of the source indices, and
   `Fin.ext` concludes that the positions coincide.

Only the reverse implication is mathematically true in general (two literals on
the same variable with opposite signs give distinct `Literal`s but repeated
indices); the forward one survives only because the hypothesis is in scope.

**Used in.** `NOrCircuit.clauseToTerm_nodup` (by `convert`) and
`NOrCircuit.toDNF_terms_nodup`, which supplies the `Nodup` side condition the
switching lemma imposes on DNF terms.
