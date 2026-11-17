<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.coeff_binaryLowPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Low Polynomial Coefficients

**Claim.** The coefficient of $X^d$ in the binary low polynomial is $a_d$ if $d<\ell$, and is zero otherwise.

**Proof.** Expand the coefficient of the finite sum defining the polynomial as the sum of the coefficients of its terms, and use the coefficient formula for a scalar multiple of a monomial. If $d<\ell$, the unique term whose exponent is $d$ is indexed by the element of $\mathrm{Fin}(\ell)$ corresponding to $d$; it contributes $a_d$, while every other term contributes zero. If $d\geq\ell$, no index has exponent $d$, so every term contributes zero. These give the two stated cases.
