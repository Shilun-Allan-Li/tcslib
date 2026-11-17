<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryLowPolynomial_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of the constant-one polynomial

**Claim.** For $\ell>0$, the low polynomial of $a$ equals $1$ exactly when $a_0=1$ and every positive-degree coordinate of $a$ is zero.

**Proof.** For the forward implication, apply equality of polynomials to their coefficients in each degree. The coefficient of the constant polynomial $1$ is $1$ in degree zero and zero in every positive degree. The low-polynomial coefficient formula (`coeff_binaryLowPolynomial`) then gives precisely the stated entries of $a$, so $a$ is the vector that is $1$ at coordinate zero and zero elsewhere. Conversely, that vector has low polynomial $1$ by `binaryLowPolynomial_binaryOneCoefficients`, using $\ell>0$.

**Key facts.** `FABL.coeff_binaryLowPolynomial`, `FABL.binaryLowPolynomial_binaryOneCoefficients`.
