<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_foldl_sets_member -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A free variable occurring in the list gets fixed by the fold

**Claim.** Let `ρ_x` be the left fold of `lits` over `ρ` fixing each still-free
literal variable to `x l.var`. If `l ∈ lits` and `l.var ∈ ρ.freeVars`, then
`ρ_x l.var ≠ none`: the fold assigns `l.var` somewhere along the way. `private`.

**Proof.** Induction on `lits`, generalizing `ρ`.

1. `nil`: `l ∈ []` is absurd (`simp at hl`).
2. `cons hd tl`: `rcases List.mem_cons.mp hl`.
   - `l = hd`: `hd.var` is free, so the first step updates it to `some _`
     (`simp [Function.update]`), and
     `termSubTree_foldl_preserves_nonnone` carries that through the rest.
   - `l ∈ tl`: `split` on `hd.var ∈ ρ.freeVars`.
     * Free, and `l.var = hd.var`: the step sets `l.var` to `some _`
       (`Function.update_apply`, `if_pos`), then
       `termSubTree_foldl_preserves_nonnone`.
     * Free, and `l.var ≠ hd.var`: `l.var` is untouched, hence still in
       `freeVars` (`Function.update_apply`, `if_neg`), so `ih _ hl_tl` applies.
     * Not free: `ρ` is unchanged, so `exact ih _ hl_tl hfree`.

**Used in.** `termSubTree_foldl_numFree_lt`, to exhibit a variable that leaves
`freeVars`.
