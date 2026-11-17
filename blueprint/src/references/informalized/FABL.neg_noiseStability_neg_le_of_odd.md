<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.neg_noiseStability_neg_le_of_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-function stability bound

**Claim.** If $f$ takes values in $[-1,1]$ and is odd, then for $0\leq\delta\leq1$, the noise stability at correlation $-\delta$ satisfies $-\operatorname{Stab}_{-\delta}[f]\leq\delta$.

**Proof.** Expand the noise stability in the Fourier basis: it is the sum over coordinate subsets $S$ of $(-\delta)^{|S|}\widehat f(S)^2$ (the Fourier expansion formula, `FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`). Oddness forces every Fourier coefficient on an even-sized subset to vanish (`FABL.fourierCoeff_even_eq_zero_of_odd`). For an odd-sized subset, $(-\delta)^{|S|}=-\delta^{|S|}$, so after negating the stability, its contribution is $\delta^{|S|}\widehat f(S)^2$. Since $0\leq\delta\leq1$ and $|S|\geq1$, this is at most $\delta\widehat f(S)^2$. The even-sized contributions vanish, so summing gives an upper bound of $\delta\sum_S\widehat f(S)^2$. The squared Fourier coefficients of a function bounded by one sum to at most one (`FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`), proving the claimed bound.

**Key facts.** `FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`, `FABL.fourierCoeff_even_eq_zero_of_odd`, `FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`.
