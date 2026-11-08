<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryLowPolynomial_binaryOneCoefficients -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant polynomial from the first coordinate

**Claim.** If $\ell>0$ and the vector has value $1$ at coordinate $0$ and value $0$ at every other coordinate, its low-degree polynomial is the constant polynomial $1$.

**Proof.** Compare coefficients in degree $d$. By the coefficient formula for a low polynomial (`coeff_binaryLowPolynomial`), the coefficient is the vector entry at $d$ when $d<\ell$, and is zero otherwise. In degree zero, positivity of $\ell$ ensures coordinate zero exists, and the chosen entry is $1$. In every positive degree below $\ell$, the entry is zero; in degrees at least $\ell$, the coefficient is zero by the formula. These are exactly the coefficients of the constant polynomial $1$, so the polynomials agree.

**Key facts.** `FABL.coeff_binaryLowPolynomial`.
