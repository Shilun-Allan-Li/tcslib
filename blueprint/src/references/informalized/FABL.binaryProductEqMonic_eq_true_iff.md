<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryProductEqMonic_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Product Criterion

**Claim.** Let $\ell$ be positive and let $m,a,b$ be binary vectors of length $\ell$. The coefficient equations saying that the product of the two low-degree polynomials associated with $a$ and $b$ has the coefficients specified by the monic polynomial associated with $m$ hold if and only if those two polynomials are equal.

**Proof.** In the forward direction, the Boolean condition supplies the coefficient equations for every degree below $2\ell+1$. The convolution coefficient is the corresponding coefficient of the product, and the prescribed coefficient is that of the monic polynomial ($\texttt{binaryConvolutionCoefficient_eq_coeff_mul}$ and $\texttt{binaryMonicCoefficient_eq_coeff}$). Thus these polynomials agree in all degrees in that range. For degrees at least $2\ell+1$, both coefficients vanish: each low-degree factor has degree less than $\ell$ ($\texttt{binaryLowPolynomial_degree_lt}$), so the product has degree at most $2\ell$, while the monic polynomial has degree $\ell$ ($\texttt{binaryMonicPolynomial_degree}$). Hence all coefficients agree, which gives polynomial equality. Conversely, if the polynomials are equal, their coefficients agree at every degree; translating those coefficients back to the convolution and prescribed-coefficient expressions yields all the required equations, and therefore the Boolean condition is true.

**Key facts.** `FABL.binaryConvolutionCoefficient_eq_coeff_mul`, `FABL.binaryMonicCoefficient_eq_coeff`, `FABL.binaryLowPolynomial_degree_lt`, `FABL.binaryMonicPolynomial_degree`.
