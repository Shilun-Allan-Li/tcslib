<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: indicator_subset_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The event `T ⊆ freeVars` factors coordinatewise

**Claim.** For a restriction `ρ : Restriction n` and `T : Finset (Fin n)`, the
`0/1` indicator of `T ⊆ ρ.freeVars` equals the product over all `i : Fin n` of
the local factor `if i ∈ T then (if ρ i = none then 1 else 0) else 1`. A purely
bookkeeping identity: it rewrites one global event as a product of independent
per-coordinate events, in the shape required by `sum_bernoulli_prod`.

**Proof.** `by_cases h : T ⊆ ρ.freeVars`.

1. If `h` holds, the left side is `1` (`if_pos`) and every factor is `1`
   (`Finset.prod_eq_one`): for `i ∈ T` we get `ρ i = none` from
   `mem_freeVars.mp (h hiT)`, and for `i ∉ T` the factor is `1` by definition
   (`simp`).
2. If `h` fails, the left side is `0` (`if_neg`) and `Finset.not_subset.mp h`
   gives some `i ∈ T` with `i ∉ ρ.freeVars`, i.e. `ρ i ≠ none`
   (`mem_freeVars.mpr`). That factor is `0`, so the product vanishes
   (`Finset.prod_eq_zero`). ∎

**Used in.** `bernoulliRestrProb_subset_freeVars` — its only consumer.
