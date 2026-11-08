<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.noiseOperator_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Noise Operators

**Claim.** Applying the noise operator with parameter sigma and then with parameter rho is the same as applying it once with parameter rho times sigma.

**Proof.** It suffices to compare Fourier coefficients, since equality of all Fourier coefficients determines a function (`fourier_ext`). At a set $S$, the coefficient after applying the noise operator is multiplied by the parameter raised to $|S|$ (`fourierCoeff_noiseOperator`). Thus the two successive applications multiply the original coefficient by $\rho^{|S|}\sigma^{|S|}$. The single application with parameter $\rho\sigma$ multiplies it by $(\rho\sigma)^{|S|}$. These agree by the power rule, so the functions are equal.

**Key facts.** `FABL.fourier_ext`, `FABL.fourierCoeff_noiseOperator`.
