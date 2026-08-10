<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: binomialPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The binomial probability mass function

**Definition.** `binomialPMF nn p k : ℝ` is the real number
`C(nn,k) · p^k · (1−p)^(nn−k)`, written in Lean as
`↑(nn.choose k) * p ^ k * (1 - p) ^ (nn - k)`. For `0 ≤ p ≤ 1` it is the
probability that a `Bin(nn, p)` variable equals `k`.

**Remark.** `p` is an unconstrained real and the exponent `nn - k` is truncated
natural subtraction, so the definition is total: for `k > nn` the binomial
coefficient is `0` and the whole product vanishes, which is why sums over
`Finset.range (nn + 1)` capture the entire mass.

**Used in.** `binomialPMF_nonneg`, `binomialPMF_sum_one`,
`chernoff_binomial_upper_tail`, and as the mixing weight in
`bernoulli_decompose`.
