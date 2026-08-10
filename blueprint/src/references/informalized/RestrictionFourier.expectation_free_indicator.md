<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: expectation_free_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# One coordinate is free with probability `p`

**Claim.** For every `p : ℝ` and `i : Fin n`,
`∑ ρ : Restriction n, bernoulliRestrWeight p ρ * (if ρ i = none then 1 else 0) = p`.
That is, the Bernoulli(`p`)-expectation of the indicator that coordinate `i` is
free equals `p`. No range hypothesis on `p`.

**Proof.**

1. Instantiate `bernoulliRestrProb_subset_freeVars p {i}` and simplify the
   exponent with `Finset.card_singleton` and `pow_one`, giving
   `Pr[{i} ⊆ ρ.freeVars] = p`.
2. Identify the stated sum with that probability: after
   `unfold bernoulliRestrProb`, the summands agree termwise
   (`Finset.sum_congr`, `congr 1`, `if_congr`) because
   `{i} ⊆ ρ.freeVars ↔ ρ i = none`
   (`Finset.singleton_subset_iff`, `mem_freeVars`).
3. Chain the two steps in a `calc`. ∎

**Used in.** `expectation_card_inter`, and the diagonal case `i = j` of
`expectation_card_inter_sq`.
