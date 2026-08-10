<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: binomialPMF_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The binomial PMF is nonnegative on `[0,1]`

**Claim.** For `p : ℝ` with `0 ≤ p` and `p ≤ 1`, and any `k : ℕ`, we have
`0 ≤ binomialPMF n p k`, i.e. `0 ≤ C(n,k) · p^k · (1−p)^(n−k)`.

**Proof.** `unfold binomialPMF`, then two nested `mul_nonneg` applications
leaving three factors.

1. `↑(n.choose k) ≥ 0` by `Nat.cast_nonneg`.
2. `p ^ k ≥ 0` by `pow_nonneg hp`.
3. `(1 - p) ^ (n - k) ≥ 0` by `pow_nonneg (sub_nonneg.mpr hp1)` — this is the
   only place `p ≤ 1` is used.

**Used in.** `bernoulli_restriction_cost`, where each mixture term
`binomialPMF n p k * fixedSizeRestrProb event k` is bounded by monotonicity in
its second factor.
