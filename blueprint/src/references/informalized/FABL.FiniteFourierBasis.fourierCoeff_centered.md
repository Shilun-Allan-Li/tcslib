<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_centered -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of centered functions

**Claim.** Centering a function by subtracting its mean changes only the constant Fourier coefficient: that coefficient becomes zero, while every other Fourier coefficient remains unchanged.

**Proof.** Write the centered function as $f$ minus the constant function with value $\mathbb E[f]$. Linearity of Fourier coefficients under subtraction (\texttt{fourierCoeff_sub}) and the formula for a constant function's coefficients (\texttt{fourierCoeff_const}) reduce the claim to two cases. At the zero multi-index, the coefficient of $f$ is its mean (\texttt{fourierCoeff_zeroMultiIndex}), so subtracting the mean gives zero. At any other multi-index, a constant function has coefficient zero, so the coefficient remains that of $f$.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_sub`, `FABL.FiniteFourierBasis.fourierCoeff_const`, `FABL.FiniteFourierBasis.fourierCoeff_zeroMultiIndex`.
