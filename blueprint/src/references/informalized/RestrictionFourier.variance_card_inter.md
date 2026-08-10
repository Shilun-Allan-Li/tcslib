<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: variance_card_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Variance: `E[(p·|U| − |U ∩ J|)²] = p·|U|·(1−p)`

**Claim.** For `0 ≤ p ≤ 1` and `U : Finset (Fin n)`,
`∑ ρ, bernoulliRestrWeight p ρ * (p * U.card - ((U ∩ ρ.freeVars).card : ℝ)) ^ 2`
equals `p * U.card * (1 - p)` — the exact binomial variance of `|U ∩ J|`. The
hypotheses `0 ≤ p`, `p ≤ 1` are used only so the weights sum to `1`.

**Proof.**

1. Expand the square termwise (`hexpand`, closed by `ring`) into
   `(p|U|)² · w ρ − 2(p|U|) · (w ρ · |U ∩ J|) + w ρ · |U ∩ J|²`.
2. Split the sum along that expansion (`Finset.sum_add_distrib`,
   `Finset.sum_sub_distrib`) and pull the constants out (`← Finset.mul_sum`).
3. Substitute the three sums: `expectation_card_inter` (`= p|U|`),
   `expectation_card_inter_sq` (`= p|U| + p²(|U|² − |U|)`) and
   `bernoulliRestrWeight_sum_one p hp0 hp1` (`= 1`).
4. `ring` finishes: `p²|U|² − 2p²|U|² + p|U| + p²|U|² − p²|U| = p|U|(1 − p)`. ∎

**Used in.** `bernoulliRestrProb_card_inter_lt`, as the numerator of the
Chebyshev estimate.
