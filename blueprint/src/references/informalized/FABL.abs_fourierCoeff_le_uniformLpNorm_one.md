<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdFunctions.lean :: FABL.abs_fourierCoeff_le_uniformLpNorm_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient bounded by the first norm

**Claim.** For any function on the sign cube and any coordinate set $S$, the absolute value of its Fourier coefficient on $S$ is at most its uniform $L^1$ norm.

**Proof.** Write the Fourier coefficient as the uniform expectation of $f(x)$ times the monomial on $S$. The absolute value of an expectation is at most the expectation of the absolute value. Each monomial has square equal to $1$ (`monomial_sq`), hence absolute value $1$; consequently the integrand's absolute value is $|f(x)|$. The uniform expectation of $|f|$ is exactly the uniform $L^1$ norm, proving the inequality.

**Key facts.** `FABL.monomial_sq`.
