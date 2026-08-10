<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: bernoulliRestrProb_card_inter_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Chebyshev lower tail: `Pr[|U ∩ J| < k] ≤ 3/(4k)`

**Claim.** Let `0 ≤ p ≤ 1`, `U : Finset (Fin n)` and `k : ℕ` with `1 ≤ k` and
`3 * (k : ℝ) ≤ p * U.card`. Then
`bernoulliRestrProb p (fun ρ => (U ∩ ρ.freeVars).card < k) ≤ 3 / (4 * k)`.

**Proof.**

1. From `1 ≤ k` and `3k ≤ p|U|` we get `0 < p * U.card - k` (`hdenom`,
   `linarith`), so the Chebyshev denominator is positive.
2. Pointwise bound `hpt`: the indicator of `|U ∩ J| < k` is at most
   `(p|U| − |U ∩ J|)² / (p|U| − k)²`. In the `< k` branch,
   `Nat.le_sub_one_of_lt` and casting give `|U ∩ J| ≤ k − 1`, so
   `le_div_iff₀` plus `gcongr` compares the deviation with `p|U| − k`; in the
   other branch the right side is nonneg (`positivity`).
3. Sum the pointwise bound against the nonneg weights
   (`Finset.sum_le_sum`, `mul_le_mul_of_nonneg_left`,
   `bernoulliRestrWeight_nonneg'`).
4. Pull the constant denominator out of the sum (`Finset.sum_div`,
   `mul_div_assoc`) and substitute `variance_card_inter p hp0 hp1 U`, leaving
   `p|U|(1−p) / (p|U| − k)²`.
5. Final numeric step: since `p|U| ≥ 3k`, one has `p|U| − k ≥ (2/3)p|U|` and
   `1 − p ≤ 1`, so the quotient is at most `(9/4)/(p|U|) ≤ 3/(4k)`. In Lean:
   `div_le_div_iff₀` followed by `nlinarith` with the auxiliary products
   `hfac = (p|U| − 3k)(3p|U| − k) ≥ 0` and `hdrop`. ∎

**Used in.** `bernoulliRestrProb_card_inter_ge`. The `3/(4k) ≤ 3/4 < 1` shape
replaces O'Donnell's Chernoff factor `exp(−2k/3)`; only a constant `< 1` is
needed downstream.
