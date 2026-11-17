<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.cdf_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the cumulative distribution

**Claim.** For a probability mass function on $\mathrm{Fin}\,m$, its cumulative mass below $n$ is nondecreasing in $n$.

**Proof.** Suppose $i\le j$. In the defining sum for the cumulative mass, compare each index $k$ separately. If $k<i$, then also $k<j$, so the summand is unchanged. If $k$ is not below $i$ but is below $j$, its contribution changes from zero to the nonnegative mass $p(k)$. If $k$ is not below $j$, both contributions are zero. Thus every summand at $i$ is at most the corresponding summand at $j$, and summing proves $\operatorname{cdf}(p,i)\le\operatorname{cdf}(p,j)$.
