<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: fixedSizeRestrProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Probability of an event under the fixed-size restriction model `R_k`

**Definition.** For a decidable predicate `event : Restriction n → Prop` and a
size `k`, `fixedSizeRestrProb event k : ℝ` is the counting ratio

`|{ρ ∈ fixedSizeRestrs n k | event ρ}| / |fixedSizeRestrs n k|`,

with both cardinalities cast from `ℕ` to `ℝ`. This is exactly the probability of
`event` when `ρ` is drawn uniformly from the restrictions with exactly `k` free
variables — the model written `R_k`.

**Remark.** No positivity side condition is imposed: when `k > n` the set
`fixedSizeRestrs n k` is empty and the definition evaluates to `0 / 0 = 0` under
Lean's convention. Both `fixedSizeRestrProb_nonneg` and
`fixedSizeRestrProb_le_one` therefore hold unconditionally, the latter by case
splitting on whether the denominator vanishes.

**Used in.** `bernoulli_decompose`, `bernoulli_restriction_cost` and
`bernoulli_restriction_asymptotic`, where it is the hypothesis side of the
`(5kw/n)^s` bound.
