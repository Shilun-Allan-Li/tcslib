<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryCoefficientAt_eq_coeff_binaryLowPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients of the Low-Degree Polynomial

**Claim.** For a binary vector of length $\ell$, its extended coordinate $a_d$ equals the coefficient of $X^d$ in the polynomial formed from its entries.

**Proof.** By the coefficient formula for the low-degree polynomial (`FABL.coeff_binaryLowPolynomial`), that coefficient is $a_d$ when $d<\ell$, and is $0$ otherwise. This is exactly the definition of the extended coordinate, so the two quantities agree.

**Key facts.** `FABL.coeff_binaryLowPolynomial`.
