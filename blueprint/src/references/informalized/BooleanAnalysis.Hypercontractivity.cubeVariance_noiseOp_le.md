<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.cubeVariance_noiseOp_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Decreases Variance

**Claim.** For $0\le\rho\le1$, applying the Fourier noise operator to a function on the Boolean cube does not increase its variance.

**Proof.** Express the variance of a function as the sum over nonempty subsets $S$ of the squares of its Fourier coefficients; equivalently, the empty-set term is zero (\texttt{BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier}). The noise operator multiplies the coefficient indexed by $S$ by $\rho^{|S|}$ (\texttt{BooleanAnalysis.noiseOp_fourier}), so its contribution to the variance is multiplied by $\rho^{2|S|}$. Since $0\le\rho\le1$, this factor lies between zero and one. Each squared coefficient is nonnegative, so each term in the noisy variance is at most its original counterpart. Summing these termwise inequalities proves the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier`, `BooleanAnalysis.noiseOp_fourier`.
