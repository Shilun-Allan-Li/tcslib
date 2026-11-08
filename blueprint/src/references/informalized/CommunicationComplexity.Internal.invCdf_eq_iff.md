<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.invCdf_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse CDF Characterization

**Claim.** For $x<1$, the inverse CDF equals an index $i$ exactly when $\mathrm{cdf}(p,i)\le x<\mathrm{cdf}(p,i+1)$.

**Proof.** By definition, the inverse CDF is the largest index whose cumulative probability is at most $x$. If that largest index is $i$, then its cumulative probability is at most $x$. If $i+1$ is still an index in the finite range, maximality says its cumulative probability cannot also be at most $x$, giving $x<\mathrm{cdf}(p,i+1)$. At the endpoint, $i+1=m$; the total cumulative probability there is one, and the assumed $x<1$ gives the same strict inequality.

Conversely, suppose $\mathrm{cdf}(p,i)\le x<\mathrm{cdf}(p,i+1)$. Then $i$ belongs to the set of eligible indices. Any eligible index $b$ must be at most $i$: if it were larger, monotonicity of the CDF would give $\mathrm{cdf}(p,i+1)\le\mathrm{cdf}(p,b)\le x$, contradicting the strict upper bound. Therefore $i$ is the largest eligible index, as required. The fact that cumulative probability is monotone is supplied by (\texttt{cdf\_mono}); at the endpoint, the total-mass identity is (\texttt{cdf\_one}).

**Key facts.** `CommunicationComplexity.Internal.cdf_mono`, `CommunicationComplexity.Internal.cdf_one`.
