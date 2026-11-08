<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryLowPolynomial_binaryScaleAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial of a scaled sum

**Claim.** For a scalar $b\in\mathbb F_2$ and vectors $p,a\in\mathbb F_2^\ell$, the polynomial of the coordinatewise sum $a+bp$ is the polynomial of $a$ plus $b$ times the polynomial of $p$.

**Proof.** Compare coefficients in degree $d$, using that the coefficient of a sum is the sum of the coefficients and that the coefficient of a scalar multiple is scaled by that scalar. The low-polynomial coefficient formula (`coeff_binaryLowPolynomial`) then reduces the claim to vector entries. If $d<\ell$, the coefficient on the left is $a_d+b p_d$, matching the right. If $d\ge\ell$, each low-polynomial coefficient is zero, so the two sides again agree. Equality of all coefficients gives the polynomial identity.

**Key facts.** `FABL.coeff_binaryLowPolynomial`.
