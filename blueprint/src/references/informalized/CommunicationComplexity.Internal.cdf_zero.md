<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.cdf_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CDF at Zero

**Claim.** For a probability mass function $p$ on $\mathrm{Fin}\,m$, the cumulative distribution function at zero is zero.

**Proof.** No natural number index is less than zero. Hence each summand in the definition of $\mathrm{cdf}(p,0)$ is zero, and their sum is zero.
