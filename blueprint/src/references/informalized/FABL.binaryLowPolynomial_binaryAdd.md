<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryLowPolynomial_binaryAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of the low polynomial

**Claim.** For binary coefficient vectors $a,b$ of length $\ell$, the low-degree polynomial associated with their coordinatewise sum over $\mathbb F_2$ is the sum of their associated low-degree polynomials.

**Proof.** Compare coefficients in each degree $d$. The coefficient of a sum of polynomials is the sum of the coefficients, and the coefficient formula for a low polynomial (`coeff_binaryLowPolynomial`) identifies each coefficient below degree $\ell$ with the corresponding vector entry. If $d<\ell$, the two sides therefore have coefficients $a_d+b_d$; if $d\ge\ell$, both sides have coefficient zero. Since polynomials are equal when all their coefficients agree, the result follows.

**Key facts.** `FABL.coeff_binaryLowPolynomial`.
