<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/BernoulliRestriction.lean :: bernoulliRestrWeight_nonneg' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bernoulli restriction weights are nonnegative

**Claim.** For `p : ℝ` with `0 ≤ p` and `p ≤ 1`, and any restriction
`ρ : Restriction n`, we have `0 ≤ bernoulliRestrWeight p ρ`.

**Proof.** A two-line computation after `unfold bernoulliRestrWeight`, which
exposes the product `p ^ ρ.freeVars.card * ((1 - p) / 2) ^ (n - ρ.freeVars.card)`.

1. `apply mul_nonneg` splits the product into its two factors.
2. First factor: `pow_nonneg hp _`.
3. Second factor: `pow_nonneg (div_nonneg (sub_nonneg.mpr hp1) (by norm_num)) _`
   — `hp1 : p ≤ 1` gives `0 ≤ 1 - p`, and `0 ≤ 2` by `norm_num`. ∎

**Used in.** `bernoulliRestrProb_le_one'` (nonnegativity side condition of
`mul_le_mul_of_nonneg_left` when the indicator is discarded), and as the
standard positivity side goal throughout `TCSlib/BooleanAnalysis/LMN/` —
`FourierConcentration`, `RestrictionCompose`, `RestrictionMonotonicity`,
`IterativeReduction`, `CircuitLayerReduction`, `RestrictionCardTail`,
`GateSwitching`. There is no unprimed `bernoulliRestrWeight_nonneg` in the
library.
