<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of a difference

**Claim.** The Fourier coefficient of $f-g$ at $a$ is the coefficient of $f$ at $a$ minus the coefficient of $g$ at $a$.

**Proof.** Write $f-g$ as $f+(-g)$. Additivity of Fourier coefficients turns its coefficient into the coefficient of $f$ plus that of $-g$ (FABL.FiniteFourierBasis.fourierCoeff_add). Express $-g$ as the scalar multiple $(-1)g$ and use homogeneity (FABL.FiniteFourierBasis.fourierCoeff_smul). The resulting scalar identity is the desired difference.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_add`, `FABL.FiniteFourierBasis.fourierCoeff_smul`.
