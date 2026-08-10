<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_foldl_preserves_nonnone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The assignment fold never un-fixes a variable

**Claim.** If `ρ v ≠ none`, then `ρ_x v ≠ none`, where `ρ_x` is the left fold of
`lits` over `ρ` that fixes each literal's still-free variable to `x l.var`. The
fold only ever adds assignments, so an already-fixed coordinate stays fixed.
`private`; a granular monotonicity helper.

**Proof.** Induction on `lits`, generalizing `ρ`.

1. `nil`: the fold is `ρ`, so `exact hv`.
2. `cons hd tl`: `simp only [List.foldl_cons]` then `apply ih`, leaving the
   claim for the one-step restriction, and `split` on
   `hd.var ∈ ρ.freeVars`.
   - Free: the step is `Function.update ρ hd.var (some (x hd.var))`; by
     `Function.update_apply` the value at `v` is either `some _` (when
     `v = hd.var`) or `ρ v` — `split <;> simp_all`.
   - Not free: the step is the identity, so `exact hv`.

**Used in.** `termSubTree_foldl_sets_member` and
`termSubTree_foldl_numFree_lt` (the `freeVars` monotonicity step).
