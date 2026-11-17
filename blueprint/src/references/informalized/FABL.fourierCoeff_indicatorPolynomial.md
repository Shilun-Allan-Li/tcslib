<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.fourierCoeff_indicatorPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator-polynomial coefficient

**Claim.** For a sign vector $a$, the Fourier coefficient at $S$ of its indicator polynomial is the reciprocal of the cube's cardinality times the monomial at $S$ evaluated at $a$.

**Proof.** Expand the Fourier coefficient as the uniform average over all sign vectors. The indicator-polynomial identity (`indicatorPolynomial_eq_ite`) says that the polynomial is $1$ at $a$ and $0$ everywhere else. Hence every term in the average vanishes except the term indexed by $a$, whose value is the monomial at $S$ evaluated at $a$. Dividing this single surviving term by the number of cube points gives the claimed formula.

**Key facts.** `FABL.indicatorPolynomial_eq_ite`.
