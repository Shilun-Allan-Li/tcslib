<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.sum_filter_finRange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum over a Filtered Finite Range

**Claim.** The sum of $F$ over the filtered list of elements of $\mathrm{Fin}\,m$ equals the sum over the finite set of elements satisfying the same predicate.

**Proof.** The finite range list has no repetitions, and filtering it preserves that property. Therefore its mapped sum agrees with the sum over its underlying finite set (the list-to-finite-set sum formula). The elements of that set are exactly those in $\mathrm{Finset.univ}$ satisfying $p$, so the resulting finite-set sum is the stated one.
