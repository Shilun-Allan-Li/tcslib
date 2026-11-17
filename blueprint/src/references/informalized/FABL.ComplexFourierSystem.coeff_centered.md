<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.ComplexFourierSystem.coeff_centered -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients after centering

**Claim.** The coefficient of the centered function is zero at the distinguished index and agrees with the original coefficient at every other index.

**Proof.** Write the centered function as the difference between $f$ and the constant function with value $F.mean(f)$. By linearity of Fourier coefficients under subtraction (`FABL.ComplexFourierSystem.coeff_sub`), its coefficient at $i$ is the coefficient of $f$ minus the coefficient of that constant function. The coefficient of a constant is its value at the distinguished index and zero elsewhere (`FABL.ComplexFourierSystem.coeff_const`). If $i$ is the distinguished index, the mean equals the coefficient of $f$ there (`FABL.ComplexFourierSystem.mean_eq_coeff_zero`), so the difference is zero. At every other index, the constant contributes zero, leaving the coefficient of $f$ unchanged.

**Key facts.** `FABL.ComplexFourierSystem.coeff_sub`, `FABL.ComplexFourierSystem.coeff_const`, `FABL.ComplexFourierSystem.mean_eq_coeff_zero`.
