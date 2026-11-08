<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.fourierCoeff_onePointFlippedParity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients of flipped parity

**Claim.** For the Boolean function that equals the full parity character except that its value is negated at the all-ones input, the Fourier coefficient at $S$ is $1-2^{-k}$ when $S$ is the full coordinate set and is $-2^{-k}$ otherwise.

**Proof.** The real-valued flipped-parity function is the full parity character minus the function that is $2$ at the all-ones input and $0$ elsewhere (`onePointFlippedParity_toReal`). By linearity of Fourier coefficients (`fourierCoeff_sub`), its coefficient is the coefficient of full parity minus that of this point-mass term. Full parity is the monomial on all coordinates (`parityFunction_toReal`), whose coefficient at $S$ is $1$ when $S$ is the full set and $0$ otherwise (`fourierCoeff_monomial`). The point-mass term has coefficient $2^{-k}$ at every $S$ (`fourierCoeff_two_mul_allOnePointMass`). Subtracting yields the two stated cases.

**Key facts.** `FABL.onePointFlippedParity_toReal`, `FABL.fourierCoeff_sub`, `FABL.parityFunction_toReal`, `FABL.fourierCoeff_monomial`, `FABL.fourierCoeff_two_mul_allOnePointMass`.
