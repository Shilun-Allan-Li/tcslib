<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.fourierCoeff_two_mul_allOnePointMass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of a point mass

**Claim.** On the $(k+1)$-dimensional Boolean cube, the function equal to $2$ at the all-one vector and $0$ elsewhere has Fourier coefficient $2^{-k}$ at every subset of coordinates.

**Proof.** Write the Fourier coefficient as the uniform average over the cube, namely the sum of the function times the corresponding monomial divided by the cube's size. The cube has $2^{k+1}$ points. Every term vanishes except at the all-one vector, where the function is $2$ and every coordinate sign is $1$, so the monomial is $1$. Thus the coefficient is $2/2^{k+1}=2^{-k}$.
