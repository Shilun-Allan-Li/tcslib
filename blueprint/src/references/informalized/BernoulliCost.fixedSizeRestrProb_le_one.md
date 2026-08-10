<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: fixedSizeRestrProb_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `fixedSizeRestrProb` is at most one

**Claim.** For every decidable predicate `event : Restriction n → Prop` and
every `k : ℕ`, `fixedSizeRestrProb event k ≤ 1`.

**Proof.** After `unfold fixedSizeRestrProb`, split on the denominator with
`Nat.eq_zero_or_pos (fixedSizeRestrs n k).card`.

1. If `(fixedSizeRestrs n k).card = 0` the quotient is `x / 0 = 0 ≤ 1`; closed by
   `simp [h]`.
2. Otherwise the denominator is a positive cast, so `div_le_one` (with
   `Nat.cast_pos.mpr h`) reduces the goal to comparing the two cardinalities.
3. The numerator counts a `Finset.filter` of the denominator's set, so
   `Finset.card_filter_le` gives the `ℕ`-inequality, transported by
   `Nat.cast_le.mpr`.

**Used in.** `bernoulli_restriction_cost`, to bound the high-`k` tail terms by
their binomial weight alone.
