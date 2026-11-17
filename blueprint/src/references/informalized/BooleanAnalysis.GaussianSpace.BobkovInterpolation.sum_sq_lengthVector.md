<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Tensorization.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.sum_sq_lengthVector -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared length decomposition

**Claim.** The sum of the squared coordinates of $V(f,g)(x)$ is the sum of the squared coordinate half-differences of $f$ and the squared values of the functions $g_j$ at $x$.

**Proof.** Split the sum over the concatenated index set of size $n+m$ into its first $n$ and last $m$ coordinates. By the definition of the concatenated vector, these coordinates are respectively $D_i f(x)$ and $g_j(x)$. Summing their squares gives the two sums on the right-hand side.
