<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.fourierCoeff_correlationImmuneAndExample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients of the Example

**Claim.** **Example 6.16.** Any parity $\chi_S$ with $|S|=k+1$ is $k$-resilient; so is $\chi_Sg$ when Boolean-valued $g$ is independent of coordinates in $S$. A correlation-immune but non-resilient example is $h=\chi_{\{1,\ldots,2m\}}\wedge\chi_{\{m+1,\ldots,3m\}}$ on $3m$ coordinates; it is true on only a fraction of inputs, so is biased.

**Proof.** First rewrite the real-valued version of the example as one half of the sum of four terms: the constant monomial, the monomial on the first block, the monomial on the last block, and the negative monomial on their symmetric difference (`correlationImmuneAndExample_toReal`). Multiply by the monomial indexed by $T$ and distribute. Linearity of expectation, together with moving the common factor $1/2$ outside, expresses the desired coefficient as half the sum of four expected monomial products. The expectation of a monomial is $1$ for the empty coordinate set and $0$ otherwise (`expect_monomial`); the expectation of a product of two monomials is $1$ when their coordinate sets coincide and $0$ otherwise (`expect_monomial_mul`). Applying these identities to the four terms gives the stated indicators and hence the formula.

**Key facts.** `FABL.correlationImmuneAndExample_toReal`, `FABL.expect_monomial`, `FABL.expect_monomial_mul`.
