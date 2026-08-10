<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: numFree_update_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fixing a free variable strictly decreases the number of free variables

**Claim.** Let `ρ : Restriction n` and let `v : Fin n` be free in `ρ`
(`hv : v ∈ ρ.freeVars`). Then for any `b : Bool`,
`Restriction.numFree (Function.update ρ v (some b)) < ρ.numFree`.

**Proof.** Unfold `numFree` to a cardinality and use `Finset.card_lt_card`, so
it suffices to prove the strict inclusion
`(Function.update ρ v (some b)).freeVars ⊂ ρ.freeVars`, split by
`ssubset_iff_subset_ne` into inclusion plus inequality.

1. **Inclusion.** If `i` is free after the update then
   `Function.update ρ v (some b) i = none`; `split at hi` on `i = v` kills the
   `i = v` case (the value is `some b`, `simp at hi`) and leaves `ρ i = none`
   otherwise (`Restriction.freeVars`, `Finset.mem_filter`).
2. **Inequality.** `v` itself is not free after the update, since
   `Function.update ρ v (some b) v = some b`
   (`simp [Function.update]`). If the two sets were equal, rewriting `hv`
   through that equality would make `v` free after the update — contradiction. ∎

**Used in.** `termSubTree_cont_congr_strict` (both children of a free-variable
branch have strictly smaller `numFree`, which is what upgrades the
continuation-agreement hypothesis to the strict form) and the branch step of
`dtDepth_restrictFn_le_numFree`, where it supplies the recursion measure.
