<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: fixedSizeRestrProb_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `fixedSizeRestrProb` is nonnegative

**Claim.** For every decidable predicate `event : Restriction n → Prop` and
every `k : ℕ`, `0 ≤ fixedSizeRestrProb event k`. No hypothesis on `k` or on the
size of the restriction set is needed.

**Proof.** A two-step unfolding.

1. `unfold fixedSizeRestrProb` exposes the quotient of two `ℕ`-casts.
2. `div_nonneg` applied to `Nat.cast_nonneg _` twice: numerator and denominator
   are both casts of naturals, hence both `≥ 0`.

**Remark.** Deliberately granular — it is the bookkeeping half of the
`0 ≤ · ≤ 1` pair with `fixedSizeRestrProb_le_one`, and the `0/0 = 0` convention
means the degenerate case `k > n` needs no separate treatment.
