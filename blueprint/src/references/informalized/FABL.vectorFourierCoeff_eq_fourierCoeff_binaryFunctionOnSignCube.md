<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients Under the Sign-Cube Identification

**Claim.** The vector Fourier coefficient of $f$ at $\gamma$ equals the sign-cube Fourier coefficient of the transported function at the monomial indexed by the support of $\gamma$.

**Proof.** By definition, the vector coefficient at $\gamma$ is the binary Fourier coefficient indexed by the support of $\gamma$. The Fourier coefficient of a function transported to the sign cube at any subset equals the binary Fourier coefficient at that same subset (`FABL.fourierCoeff_binaryFunctionOnSignCube`). Applying this identity to the support of $\gamma$ gives the result.

**Key facts.** `FABL.fourierCoeff_binaryFunctionOnSignCube`.
