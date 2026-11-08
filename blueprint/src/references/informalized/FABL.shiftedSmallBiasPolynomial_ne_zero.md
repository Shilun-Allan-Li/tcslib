<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.shiftedSmallBiasPolynomial_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of the Shifted Polynomial

**Claim.** If γ is a nonzero binary vector, then the polynomial $\sum_{i=0}^{n-1}\gamma_iX^i$, with coefficients mapped into the field with $2^\ell$ elements, is nonzero.

**Proof.** Because γ is nonzero, some coordinate $i$ satisfies $\gamma_i\ne0$. The coefficient of $X^i$ in the shifted polynomial is exactly the image of $\gamma_i$ under the field embedding. This image is nonzero because the embedding is injective. A polynomial with a nonzero coefficient cannot be the zero polynomial, proving the claim.
