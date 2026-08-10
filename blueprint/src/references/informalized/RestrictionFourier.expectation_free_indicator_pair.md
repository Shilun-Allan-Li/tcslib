<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: expectation_free_indicator_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two distinct coordinates are both free with probability `p²`

**Claim.** For `p : ℝ` and `i ≠ j` in `Fin n`, the Bernoulli(`p`)-expectation of
the product of the two free-coordinate indicators,
`∑ ρ, bernoulliRestrWeight p ρ * ((if ρ i = none then 1 else 0) * (if ρ j = none then 1 else 0))`,
equals `p ^ 2`. This is the pairwise-independence input to the second moment.

**Proof.**

1. Instantiate `bernoulliRestrProb_subset_freeVars p {i, j}`; since `i ≠ j`, the
   card is `2` (`Finset.card_insert_of_notMem`, `Finset.card_singleton`), so
   `Pr[{i, j} ⊆ ρ.freeVars] = p ^ 2`.
2. Match the stated sum with that probability termwise (`unfold
   bernoulliRestrProb`, `Finset.sum_congr`, `congr 1`): the product of
   indicators is `1` exactly when `ρ i = none` and `ρ j = none`, which is
   `{i, j} ⊆ ρ.freeVars` — checked by `by_cases` on both conditions plus
   `simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_freeVars]`.
3. Conclude by `calc`. ∎

**Used in.** the off-diagonal case of `expectation_card_inter_sq`.
