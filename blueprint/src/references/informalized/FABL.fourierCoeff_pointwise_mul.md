<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/CorrelationImmunityBounds.lean :: FABL.fourierCoeff_pointwise_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of a product

**Claim.** The Fourier coefficient of the pointwise product $fg$ at $S$ is $\sum_T\widehat f(T\triangle S)\widehat g(T)$.

**Proof.** Expand $g$ in its Fourier series, $g(x)=\sum_T\widehat g(T)\chi_T(x)$, using the Fourier expansion identity (`fourier_expansion`). Substitute this into the expectation defining the coefficient of $fg$ and distribute the finite sum. Multiplying the character at $T$ by the character at $S$ gives the character at $T\triangle S$ (`monomial_mul_monomial`). Interchange the finite sum and expectation. For each $T$, factor out the scalar $\widehat g(T)$; the remaining expectation is the coefficient of $f$ at $T\triangle S$. Summing these terms gives the formula.

**Key facts.** `FABL.fourier_expansion`, `FABL.monomial_mul_monomial`.
