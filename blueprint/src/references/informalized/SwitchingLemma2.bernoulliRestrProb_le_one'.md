<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/BernoulliRestriction.lean :: bernoulliRestrProb_le_one' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bernoulli restriction probabilities are at most one

**Claim.** For `p : ℝ` with `0 ≤ p` and `p ≤ 1`, and any predicate
`event : Restriction n → Prop` with `[DecidablePred event]`,
`bernoulliRestrProb p event ≤ 1`.

**Proof.** `unfold bernoulliRestrProb`, then a two-step `calc` on the sum
`∑ ρ, bernoulliRestrWeight p ρ * (if event ρ then 1 else 0)`.

1. Drop the indicator: `Finset.sum_le_sum` reduces to a pointwise bound at each
   `ρ`. There `(if event ρ then (1:ℝ) else 0) ≤ 1` by `split_ifs <;> norm_num`
   (`h1`), so `mul_le_mul_of_nonneg_left h1 (bernoulliRestrWeight_nonneg' p hp hp1 ρ)`
   gives `weight * indicator ≤ weight * 1`, and `ring` finishes
   `weight * 1 = weight`.
2. The resulting total is exactly `1` by `bernoulliRestrWeight_sum_one p hp hp1`. ∎

**Used in.** `LMN/RestrictionCompose.lean`, `LMN/RestrictionMonotonicity.lean`,
`LMN/CircuitLayerReduction.lean`, `LMN/SwitchingBernoulli.lean` — the trivial
upper bound used whenever an inner conditional probability is discarded from a
nested restriction sum.
