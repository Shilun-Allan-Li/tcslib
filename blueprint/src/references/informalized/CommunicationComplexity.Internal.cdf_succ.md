<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.cdf_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CDF Successor Recurrence

**Claim.** For a probability mass function $p$ on $\mathrm{Fin}\,m$ and an index $n\in\mathrm{Fin}\,m$, the cumulative distribution function satisfies $\mathrm{cdf}(p,n+1)=\mathrm{cdf}(p,n)+p(n)$.

**Proof.** For each index $j$, the condition $j<n+1$ holds exactly when either $j<n$ or $j=n$. Accordingly, its contribution to the sum defining $\mathrm{cdf}(p,n+1)$ is the contribution to $\mathrm{cdf}(p,n)$ plus the contribution that is $p(n)$ when $j=n$ and zero otherwise. Summing this identity over all indices separates the sum into two finite sums. The first is $\mathrm{cdf}(p,n)$, and the second contains only the index $n$, so it equals $p(n)$.
