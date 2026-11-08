<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.tendsto_stableInfluencePolynomial_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Limit of the Stable Influence Polynomial

**Claim.** As the parameter tends to zero, the stable influence polynomial tends to the sum of squared Fourier coefficients over the multi-indices of order one that are nonzero at the specified coordinate.

**Proof.** The value of the stable influence polynomial at zero is exactly the stated sum (`stableInfluencePolynomial_zero`). The polynomial is continuous in its parameter (`continuous_stableInfluencePolynomial`), so continuity at zero implies that its values tend to that value as the parameter tends to zero.

**Key facts.** `FABL.FiniteFourierBasis.stableInfluencePolynomial_zero`, `FABL.continuous_stableInfluencePolynomial`.
