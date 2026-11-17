<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierEstimator.lean :: FABL.fourierCoeff_pointwise_mul_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication shifts Fourier support

**Claim.** The Fourier coefficient at $S$ of $x\mapsto f(x)\prod_{i\in U}x_i$ equals $\widehat f(U\triangle S)$.

**Proof.** In the expectation defining the coefficient at $S$, the integrand contains $f(x)$ times the monomial on $U$ and the monomial on $S$. Associativity groups the two monomial factors, and their product is the monomial on $U\triangle S$ (`monomial_mul_monomial`). The resulting expectation is precisely the coefficient of $f$ at $U\triangle S$.

**Key facts.** `FABL.monomial_mul_monomial`.
