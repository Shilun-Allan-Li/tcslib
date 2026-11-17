<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.cdf_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Cumulative Probability

**Claim.** For a probability mass function on the finite set of indices, the cumulative distribution function at the endpoint equals one.

**Proof.** At the endpoint, every index $j\in\mathrm{Fin}\,m$ satisfies $j<m$. Thus every summand in the definition of the cumulative distribution function is $p(j)$, so the finite sum is the total mass of the probability mass function. That total mass is one.
