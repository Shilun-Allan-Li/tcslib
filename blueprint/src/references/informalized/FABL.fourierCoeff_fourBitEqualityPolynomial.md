<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdFunctions.lean :: FABL.fourierCoeff_fourBitEqualityPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Four-Bit Equality Polynomial Coefficients

**Claim.** For every subset $S$ of the four coordinates, the Fourier coefficient of the polynomial is $-3$ when $S$ is empty, $1$ when $S$ has two elements, and $0$ otherwise.

**Proof.** The polynomial is first expressed as the multilinear polynomial whose coefficient function assigns $-3$ to the empty set, $1$ to each of the six two-element sets, and $0$ to every other frequency (`fourBitEqualityPolynomial_expansion`). Fourier expansion uniqueness (`fourier_expansion_unique`) says that the coefficient function in any such expansion must equal the Fourier coefficient function. Evaluating that equality at $S$ gives the stated cases.

**Key facts.** `FABL.fourBitEqualityPolynomial_expansion`, `FABL.fourier_expansion_unique`.
