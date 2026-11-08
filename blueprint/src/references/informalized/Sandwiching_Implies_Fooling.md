<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: Sandwiching_Implies_Fooling -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sandwiching Polynomials Fool Independent Distributions

**Claim.** If a function is bounded pointwise by degree-at-most-$k$ polynomials whose uniform-average gap is at most $\varepsilon$, then every $k$-wise independent distribution has expectation of the function within $\varepsilon$ of its uniform expectation.

**Proof.** Let $P_\ell\le f\le P_u$ be the given sandwich. Since each polynomial has degree at most $k$, the expectation-matching theorem for $k$-wise independent distributions (`KWise_Fools_Polynomial`) gives the same expectation under the distribution and under uniform measure for both $P_\ell$ and $P_u$. Pointwise comparison and monotonicity of finite weighted sums then bound the difference of the two expectations of $f$ above by the uniform expectation of $P_u-P_\ell$, and below by its negative. The assumed bound on the uniform-average gap makes both bounds at most $\varepsilon$, which is exactly the asserted absolute-value estimate.

**Key facts.** `KWise_Fools_Polynomial`.
