<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryConvolutionCoefficient_eq_coeff_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of a Binary Polynomial Product

**Claim.** The coefficient of degree $d$ in the product of the two low-degree polynomials is the sum of $a_i b_j$ over pairs of nonnegative indices with $i+j=d$, with terms taken to be zero when either index is outside the allowed range.

**Proof.** The coefficient of degree $d$ in a product of polynomials is the sum, over the antidiagonal $i+j=d$, of the product of the degree-$i$ coefficient of the first polynomial and the degree-$j$ coefficient of the second (`Polynomial.coeff_mul`). By the coefficient formula for each low-degree polynomial (`FABL.coeff_binaryLowPolynomial`), these coefficients are the corresponding vector entries when their indices are below $\ell$, and zero otherwise. Thus each summand is precisely the indicated product when both indices are allowed, and zero when either is not. Summing gives the stated convolution coefficient.

**Key facts.** `FABL.coeff_binaryLowPolynomial`.
