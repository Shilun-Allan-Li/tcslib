<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.fourierCoeff_andFunction_of_ne_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Coefficients of Conjunction

**Claim.** For every nonempty coordinate set $S$, the conjunction function has Fourier coefficient $-2\cdot 2^{-w}(-1)^{|S|}$.

**Proof.** Write the conjunction as $1-2$ times the indicator of the all-$-1$ input. Multiplying by the monomial for $S$ expresses the integrand as that monomial minus twice the monomial restricted to the all-$-1$ input. The expectation of the first term is zero because $S$ is nonempty (FABL.expect_monomial). The restricted term vanishes except at the unique all-$-1$ point; there the monomial is $(-1)^{|S|}$, and the point has uniform probability $2^{-w}$. Thus the coefficient is $-2\cdot 2^{-w}(-1)^{|S|}$.

**Key facts.** `FABL.expect_monomial`.
