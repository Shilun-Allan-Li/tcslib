<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.constantPairBooleanFunction_isCorrelationImmune -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlation Immunity of the Constant-Pair Function

**Claim.** The sign-valued function obtained from the indicator of the zero and all-ones binary vectors has every nonempty Fourier coefficient indexed by at most one coordinate equal to zero.

**Proof.** Let $T$ be a nonempty set of coordinates with $|T|\leq 1$. These conditions force $|T|=1$. Encode $T$ as the binary vector supported exactly on $T$. The support of this vector is $T$, by the support-vector correspondence used in the proof. The Fourier coefficient on the sign cube equals the vector Fourier coefficient of the real sign encoding of the constant-pair indicator, by the identification formula (vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube). The real form of the sign-valued function is precisely that encoded function (constantPairBooleanFunction_toReal). The vector Fourier coefficient at a singleton support vanishes, by the constant-pair coefficient calculation (vectorFourierCoeff_realSignEncodedFunction_constantPairF₂Indicator_eq_zero). Hence the Fourier coefficient is zero, and so its absolute value is zero, as required.

**Key facts.** `FABL.constantPairBooleanFunction_toReal`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`, `FABL.vectorFourierCoeff_realSignEncodedFunction_constantPairF₂Indicator_eq_zero`.
