<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: KWise_Fools_Monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# K-wise independence and monomials

**Claim.** If $\mu$ has uniform joint distribution on every set of at most $k$ coordinates, then for every set $S$ of at most $k$ coordinates, the expectation of the monomial associated with $S$ under $\mu$ equals its uniform-cube expectation.

**Proof.** The monomial associated with $S$ is the indicator of the event that every coordinate in $S$ equals true: it is $1$ on that event and $0$ otherwise. The joint distribution of the coordinates in $S$ under $\mu$ is uniform by $k$-wise independence, since $|S|\le k$. Thus the probability of the all-true assignment on these coordinates is the same under $\mu$ as under the uniform cube distribution. The expectation of the indicator, and hence of the monomial, equals that probability in each distribution, proving the equality.
