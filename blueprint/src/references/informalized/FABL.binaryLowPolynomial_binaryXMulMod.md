<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryLowPolynomial_binaryXMulMod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial of the shifted coefficients

**Claim.** For $\ell>0$, the polynomial of the vector formed by shifting $a$ up one degree and adding its top coefficient times $m$ equals $X$ times the polynomial of $a$ plus that top coefficient times the monic polynomial associated with $m$.

**Proof.** Compare coefficients in degree $d$. The coefficient of the sum on the right splits into the coefficient of $X$ times the low polynomial of $a$ and the coefficient of the scaled monic polynomial. Convert low-polynomial coefficients to vector coefficients using `binaryCoefficientAt_eq_coeff_binaryLowPolynomial`, and monic-polynomial coefficients using `binaryMonicCoefficient_eq_coeff`. The coefficient of the constructed vector is the shifted coefficient of $a$ plus its top coefficient times the monic coefficient of $m$, by `binaryCoefficientAt_binaryXMulMod`. Finally, `binaryShiftUpCoefficient_eq_coeff_X_mul` identifies the shifted term with the coefficient of $X$ times the low polynomial of $a$. Thus the coefficients agree in every degree, proving the identity.

**Key facts.** `FABL.binaryCoefficientAt_eq_coeff_binaryLowPolynomial`, `FABL.binaryCoefficientAt_binaryXMulMod`, `FABL.binaryShiftUpCoefficient_eq_coeff_X_mul`, `FABL.binaryMonicCoefficient_eq_coeff`.
