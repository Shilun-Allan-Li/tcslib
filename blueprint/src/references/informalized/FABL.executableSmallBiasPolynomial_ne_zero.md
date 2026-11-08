<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.executableSmallBiasPolynomial_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of the encoded polynomial

**Claim.** If $\gamma$ is nonzero, then its encoded polynomial over the quotient field is nonzero.

**Proof.** Because $\gamma\ne 0$, there is an index $i$ for which $\gamma_i\ne 0$. In the encoded polynomial, the coefficient of $X^{i+1}$ is exactly the image of $\gamma_i$ under the field map into the quotient field. This image is nonzero because the map is injective. A zero polynomial has every coefficient zero, so the encoded polynomial cannot be zero.
