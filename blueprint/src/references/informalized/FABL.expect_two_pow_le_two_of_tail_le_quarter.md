<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.expect_two_pow_le_two_of_tail_le_quarter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Depth Bound from Tail Estimates

**Claim.** If the depth is bounded by $N$ and the probability that it is at least $k$ is at most $(1/4)^k$ for every $k$, then the random-restriction average of $2^d$ is at most $2$.

**Proof.** For each restriction, the bound $d\le N$ allows the exact expansion $2^d=1+\sum_{j=0}^{N-1}2^j\mathbf 1_{\	ext{depth}\ge j+1}$ (`two_pow_eq_one_add_sum_tailIndicators`). Average this identity. Additivity, preservation of constants, finite-sum linearity, and extraction of a constant factor from the random-restriction average (`expectRandomRestriction_add`, `expectRandomRestriction_const`, `expectRandomRestriction_sum`, and `expectRandomRestriction_const_mul`) turn the result into $1+\sum_{j<N}2^j\Pr[d\ge j+1]$. Use the tail hypothesis to bound this by $1+\sum_{j<N}2^j(1/4)^{j+1}$. Each summand equals $(1/4)(1/2)^j$ (`two_pow_mul_quarter_pow_succ`). The finite geometric sum of $(1/2)^j$ is at most $2$, so the whole expression is at most $1+(1/4)2\le2$.

**Key facts.** `FABL.two_pow_eq_one_add_sum_tailIndicators`, `FABL.expectRandomRestriction_add`, `FABL.expectRandomRestriction_const`, `FABL.expectRandomRestriction_sum`, `FABL.expectRandomRestriction_const_mul`, `FABL.two_pow_mul_quarter_pow_succ`.
