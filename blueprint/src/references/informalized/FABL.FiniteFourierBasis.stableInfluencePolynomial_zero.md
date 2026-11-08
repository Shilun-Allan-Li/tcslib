<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.stableInfluencePolynomial_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence polynomial at zero

**Claim.** At parameter zero, the stable influence polynomial at coordinate $i$ is the sum of squared Fourier coefficients over multi-indices of order one that are nonconstant at $i$.

**Proof.** Expand the stable influence polynomial and filter its sum by whether the index at $i$ is nonconstant. If it is constant, the term is excluded. Otherwise the support contains $i$, so the order is positive (multiIndexOrder_pos_of_ne). When that order is one, the exponent in the weight is zero and the term is the squared Fourier coefficient. When the order is not one, positivity of the order implies that its predecessor is positive; the zero parameter raised to this positive exponent makes the term vanish. The surviving terms are exactly those with order one and nonconstant index at $i$.

**Key facts.** `FABL.multiIndexOrder_pos_of_ne`.
