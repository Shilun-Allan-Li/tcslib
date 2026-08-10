<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: binomialPMF_sum_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The binomial PMF sums to one

**Claim.** For any `p : ℝ`, `∑ k ∈ Finset.range (n + 1), binomialPMF n p k = 1`.
The hypotheses `0 ≤ p` and `p ≤ 1` appear in the signature but are named
`_hp`/`_hp1` and go unused — the identity is a polynomial one, valid for every
real `p`.

**Proof.** Essentially one rewrite.

1. `unfold binomialPMF` turns the sum into
   `∑ k ∈ range (n+1), C(n,k) · p^k · (1−p)^(n−k)`.
2. `add_pow p (1 - p) n` is the binomial theorem: `(p + (1−p))^n` equals that
   sum.
3. `simpa [mul_assoc, mul_comm, mul_left_comm] using this.symm` matches the two
   sides up to reassociation of the three factors and simplifies
   `(p + (1 − p))^n = 1^n = 1`.

**Used in.** `bernoulli_restriction_cost`, to bound the truncated low-`k` sum
`∑ k, if k ≤ 2np then binomialPMF n p k else 0` by `1` before factoring out
`(10pw)^s`.
