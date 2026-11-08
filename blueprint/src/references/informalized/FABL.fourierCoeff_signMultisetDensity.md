<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.fourierCoeff_signMultisetDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical Sign Distribution Coefficients

**Claim.** The Fourier coefficient at $S$ of the sign-cube density induced by a uniform element of a finite nonempty set is the uniform average over that set of the parity character on $S$ evaluated at the assigned sign vector.

**Proof.** First translate the Fourier coefficient of the sign-cube function into the corresponding binary-cube Fourier coefficient (`fourierCoeff_binaryFunctionOnSignCube`). Express that coefficient as the density's expectation of the character. The expectation formula for a uniform pushforward identifies it with the uniform average over the original finite set (`ProbabilityDensity.expectation_uniformPushforward`). Finally, the parity character of the binary encoding of each assigned sign vector equals its sign-cube monomial (`monomial_binaryCubeSignEquiv`), giving the stated average.

**Key facts.** `FABL.fourierCoeff_binaryFunctionOnSignCube`, `FABL.ProbabilityDensity.expectation_uniformPushforward`, `FABL.monomial_binaryCubeSignEquiv`.
