<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.vectorFourierCoeff_realSignEncodedFunction_constantPairF₂Indicator_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing coefficient for a singleton support

**Claim.** If $T$ has one coordinate, the vector Fourier coefficient at the binary vector supported on $T$ of the real sign encoding of the constant-pair indicator is zero.

**Proof.** Write $T=\{i\}$ and let $\gamma$ be its indicator vector. This vector is nonzero, and the one-coordinate support criterion shows that it does not lie in the perpendicular subspace of the constant-pair subspace. The real sign encoding of the constant-pair indicator equals $1-2$ times the indicator of that subspace. In the Fourier expectation, distribute this expression into the constant term and the subspace-indicator term. The constant term has coefficient zero at nonzero $\gamma$, by Walsh-character orthogonality. The other term has coefficient zero because $\gamma$ is outside the perpendicular subspace. Hence the original coefficient is zero.

**Key facts.** `FABL.f₂CubeOfFinset_apply`, `FABL.f₂CubeOfFinset_not_mem_perpendicular_constantPairSubspace_of_card_one`, `FABL.realSignEncodedFunction_constantPairF₂Indicator`, `FABL.vectorFourierCoeff_eq_expect`, `FABL.expect_vectorWalshCharacter`, `FABL.vectorFourierCoeff_setIndicator_submodule_of_not_mem`.
