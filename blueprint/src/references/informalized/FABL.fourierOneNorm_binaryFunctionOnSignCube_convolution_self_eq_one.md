<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.fourierOneNorm_binaryFunctionOnSignCube_convolution_self_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of self-convolution

**Claim.** If $f:(\mathbb F_2)^n\to\mathbb R$ is sign-valued, then the Fourier one norm of the sign-cube function corresponding to its normalized self-convolution is $1$.

**Proof.** Reindex the sum over sign-cube frequencies by the bijection between subsets of coordinates and vectors in $(\mathbb F_2)^n$. The correspondence theorem identifies each sign-cube Fourier coefficient of the transported convolution with the corresponding vector Fourier coefficient. For each frequency, the convolution theorem says that this coefficient is the product of the two coefficients of $f$; for self-convolution it is therefore the square of that real coefficient. Taking absolute values turns the square into the same square, since $|a^2|=a^2$. Summing over frequencies gives $1$ by Parseval's identity for a sign-valued function (`sum_sq_vectorFourierCoeff_eq_one`).

**Key facts.** `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`, `FABL.vectorFourierCoeff_convolution`, `FABL.sum_sq_vectorFourierCoeff_eq_one`.
