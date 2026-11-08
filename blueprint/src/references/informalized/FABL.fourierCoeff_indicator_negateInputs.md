<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.fourierCoeff_indicator_negateInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients under input negation

**Claim.** Negating the inputs prescribed by ${\sigma}$ multiplies the Fourier coefficient at $S$ by the product of $-1$ over the negated coordinates in $S$, with factor $1$ at the other coordinates.

**Proof.** Reindex the uniform average by the bijection that negates exactly the coordinates selected by ${\sigma}$. Under this change of variables, the predicate indicator becomes the original predicate's indicator. The monomial transforms by the factor ${\prod_{i\in S}}(-1)$ for selected coordinates and $1$ for the others (`monomial_signInputNegationEquiv`). This factor is independent of the input, so it can be pulled outside the expectation, leaving the original Fourier coefficient multiplied by the stated product.

**Key facts.** `FABL.monomial_signInputNegationEquiv`.
