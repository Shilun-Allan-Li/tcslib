<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_foldl_numFree_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The assignment fold strictly decreases `numFree`

**Claim.** Let `ρ_x` be the left fold of `lits` over `ρ` fixing each still-free
literal variable to `x l.var`. If some `l ∈ lits` has `l.var ∈ ρ.freeVars`, then
`ρ_x.numFree < ρ.numFree`. `private`; this is the termination measure behind the
fuel bound for `canonicalDTree.go`.

**Proof.** Abbreviate `ρ' := ρ_x` (`set`).

1. `ρ'.freeVars ⊆ ρ.freeVars`: a coordinate free in `ρ'` must have been free in
   `ρ`, since otherwise `termSubTree_foldl_preserves_nonnone` would keep it
   fixed (`by_contra`, `push_neg`).
2. `l.var ∉ ρ'.freeVars`: by `termSubTree_foldl_sets_member`, the fold assigns
   `l.var`, so it is no longer `none`.
3. The inclusion is therefore strict — `hsub.ssubset_of_ne` using `hfree`
   together with step 2 — and `Finset.card_lt_card` gives the claim.

**Used in.** `canonicalDTree_go_correct`, to show the recursive call's
restriction has `numFree < k` so the fuel suffices.
