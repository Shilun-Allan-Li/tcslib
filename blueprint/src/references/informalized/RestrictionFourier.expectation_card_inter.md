<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: expectation_card_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# First moment: `E[|U ∩ J|] = p·|U|`

**Claim.** For every `p : ℝ` and `U : Finset (Fin n)`,
`∑ ρ, bernoulliRestrWeight p ρ * ((U ∩ ρ.freeVars).card : ℝ) = p * U.card`.
The expected number of coordinates of `U` left free by a Bernoulli(`p`)
restriction is `p·|U|`; no hypothesis on `p` is required.

**Proof.**

1. Rewrite each summand by `card_inter_eq_sum` and distribute the weight with
   `Finset.mul_sum`, giving a double sum over `ρ` and `i ∈ U`.
2. Exchange the order of summation (`Finset.sum_comm`).
3. The inner sum over `ρ` is `p` for each `i`, by
   `expectation_free_indicator p i`.
4. Summing the constant `p` over `U` gives `p * U.card`
   (`Finset.sum_const`, `nsmul_eq_mul`, `mul_comm`). ∎

**Used in.** `variance_card_inter`.
