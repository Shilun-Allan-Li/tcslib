<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierFormulas.lean :: FABL.noiseStability_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability of a Monomial

**Claim.** For every correlation parameter $\rho\in[-1,1]$ and every coordinate set $S$, the noise stability of the monomial indexed by $S$ is $\rho^{|S|}$.

**Proof.** Expand noise stability in the Fourier basis: it is the sum, over all coordinate sets $T$, of $\rho^{|T|}$ times the square of the Fourier coefficient at $T$ (`noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`). The monomial indexed by $S$ has Fourier coefficient $1$ at $S$ and $0$ at every other set (`fourierCoeff_monomial`). Thus every term vanishes except the one for $T=S$, which equals $\rho^{|S|}$.

**Key facts.** `FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`, `FABL.fourierCoeff_monomial`.
