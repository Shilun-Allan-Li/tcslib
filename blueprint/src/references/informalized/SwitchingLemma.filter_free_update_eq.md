<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: filter_free_update_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Updating one variable does not change which other literals are free

**Claim.** Let `rest : List (Literal n)`, `ρ : Restriction n`, `v : Fin n`,
`b : Bool`, and suppose no literal of `rest` mentions `v`
(`hdist : ∀ l ∈ rest, l.var ≠ v`). Then filtering `rest` by freeness under
`Function.update ρ v (some b)` gives the same list as filtering by freeness
under `ρ`.

**Proof.** Two steps.

1. For each `l ∈ rest`, the two membership propositions coincide:
   `l.var ∈ (Function.update ρ v (some b)).freeVars` iff
   `l.var ∈ ρ.freeVars`, because `Function.update` alters the restriction only
   at `v` and `l.var ≠ v` (`unfold Restriction.freeVars; aesop`).
2. Pointwise agreement of the two decidable predicates on the members of `rest`
   transfers to the filters (`List.filter_congr`, discharging the `decide`
   wrapper with `aesop`). ∎

**Used in.** `termSubTree_deepPath_var_match`, `termSubTree_deepPath_append`,
and `termSubTree_deepPath_split` — each recursive step of `termSubTree` fixes
the head variable, and this lemma says the free-literal count of the tail is
unaffected, provided the term's variables are pairwise distinct. Also used by
`processClauseLits_termSubTree_drop` in
`TCSlib/BooleanAnalysis/Switching.lean`.
