<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.noiseStability_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability Is Unchanged by Sign Reversal

**Claim.** For every $\rho\in[-1,1]$ and every real-valued function $f$ on the Boolean cube, the noise stability of $-f$ equals that of $f$.

**Proof.** Write each stability as its Fourier expansion, a sum of $\rho^{|S|}$ times squared Fourier coefficients. The coefficient of $-f$ at each set $S$ is the negative of the coefficient of $f$: this follows from linearity of the uniform average defining the coefficient. Squaring removes this sign, so the two expansions agree term by term, and hence their sums are equal.

**Key facts.** `FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`.
