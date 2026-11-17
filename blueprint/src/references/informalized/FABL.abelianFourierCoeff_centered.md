<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.abelianFourierCoeff_centered -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients After Centering

**Claim.** Subtracting the uniform mean from a function makes its Fourier coefficient at the trivial character zero and leaves its coefficients at all nontrivial characters unchanged.

**Proof.** Write the centered function as $f$ minus the constant function with value $\operatorname{Mean}(f)$. Fourier coefficients are additive over differences (`FABL.abelianFourierCoeff_sub`), and the coefficient of a constant is its value at the trivial character and zero otherwise (`FABL.abelianFourierCoeff_const`). If $\chi$ is nontrivial, the constant term therefore contributes zero, so the coefficient is unchanged. If $\chi$ is trivial, its coefficient on $f$ is the uniform mean of $f$ (`FABL.complexMean_eq_abelianFourierCoeff_zero`), which cancels the subtracted constant's coefficient; the centered coefficient is zero.

**Key facts.** `FABL.abelianFourierCoeff_sub`, `FABL.abelianFourierCoeff_const`, `FABL.complexMean_eq_abelianFourierCoeff_zero`.
