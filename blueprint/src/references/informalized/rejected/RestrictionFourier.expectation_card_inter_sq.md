<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: expectation_card_inter_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Second moment: `E[|U ∩ J|²] = p·|U| + p²·(|U|² − |U|)`

**Claim.** For every `p : ℝ` and `U : Finset (Fin n)`,
`∑ ρ, bernoulliRestrWeight p ρ * ((U ∩ ρ.freeVars).card : ℝ) ^ 2`
equals `p * U.card + p ^ 2 * ((U.card : ℝ) ^ 2 - U.card)`, i.e. the exact
`Binomial(|U|, p)` second moment. No hypothesis on `p`.

**Proof.**

1. Expand the square as a double sum: `pow_two`, `card_inter_eq_sum`,
   `Finset.sum_mul_sum` and `Finset.mul_sum` rewrite each `ρ`-summand as
   `∑ i ∈ U, ∑ j ∈ U, w ρ * (ind_i ρ * ind_j ρ)` (`hsq`).
2. Move the `ρ`-sum innermost by two applications of `Finset.sum_comm`.
3. Evaluate the inner `ρ`-sum as `if i = j then p else p ^ 2` (`hij`): on the
   diagonal the indicator is idempotent (`by_cases` + `simp`) and
   `expectation_free_indicator` applies; off the diagonal use
   `expectation_free_indicator_pair`.
4. Each row sums to `p ^ 2 * ((U.card : ℝ) - 1) + p` (`hrow`): write
   `if i = j then p else p ^ 2` as `p ^ 2 + (if i = j then p - p ^ 2 else 0)`
   (`split_ifs <;> ring`), then `Finset.sum_add_distrib`,
   `Finset.sum_const` and `Finset.sum_ite_eq` with `i ∈ U`.
5. Sum the rows over `U` (`Finset.sum_const`, `nsmul_eq_mul`) and finish with
   `ring`. ∎

**Used in.** `variance_card_inter`.
