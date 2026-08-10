<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_cons_nonfree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Unfolding termSubTree at an already-fixed head literal

**Claim.** If the head literal's variable is not free in `ρ`
(`hnfree : l.var ∉ ρ.freeVars`), then
`termSubTree (l :: rest) ρ cont = termSubTree rest ρ cont`: the literal is
skipped, no branch is created, and the restriction is unchanged.

**Proof.** Immediate from the defining equation: `simp [termSubTree, hnfree]`
selects the `else` branch of the `if l.var ∈ ρ.freeVars` test.

**Used in.** `termSubTree_skip_nonfree_prefix'` and
`termSubTree_skip_updated_head` (which strip a whole non-free prefix, resp. a
head that a previous update has just fixed), the non-free cases of
`termSubTree_deepPath_var_match`, `termSubTree_deepPath_append` and
`termSubTree_deepPath_split`, and `processClauseLits_termSubTree_drop` in
`TCSlib/BooleanAnalysis/Switching.lean`.
