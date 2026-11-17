<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryShiftUpCoefficient_eq_coeff_X_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of a Shifted Polynomial

**Claim.** The coefficient of degree $d$ in $XA(X)$ is zero for $d=0$, and for positive $d$ it is the coefficient of $A(X)$ in degree $d-1$.

**Proof.** Separate the degree-zero case from the positive-degree case. At degree zero, the shifted coefficient is defined to be zero, and the constant coefficient of $XA(X)$ is also zero. For $d=e+1$, multiplication by $X$ shifts polynomial coefficients up by one, so the coefficient at degree $e+1$ is the coefficient of $A(X)$ at degree $e$. The coefficient formula for the low polynomial identifies this with the coordinate-based coefficient, including the convention that it vanishes beyond the vector's range (`FABL.binaryCoefficientAt_eq_coeff_binaryLowPolynomial`).

**Key facts.** `FABL.binaryCoefficientAt_eq_coeff_binaryLowPolynomial`.
