<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean :: BooleanAnalysis.ThresholdFunctions.noise_degree_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Noise Lower Bound

**Claim.** If the coefficient family $p$ vanishes on subsets larger than $k$ and $0\le\rho\le1$, then $\rho^{2k}\sum_S p(S)^2\le\mathbb E[(T_\rho P_p)^2]$.

**Proof.** The Fourier formula for the squared norm of the noise operator gives $\mathbb E[(T_\rho P_p)^2]=\sum_S(\rho^{|S|})^2\widehat{P_p}(S)^2$ (\texttt{BooleanAnalysis.Hypercontractivity.noise_l2_fourier}); the Fourier coefficient of the represented polynomial at $S$ is $p(S)$ (\texttt{BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval}). For each $S$ with $|S|\le k$, the bounds $0\le\rho\le1$ imply $\rho^{2k}\le(\rho^{|S|})^2$, so multiplying by $p(S)^2\ge0$ gives the desired termwise lower bound. If $|S|>k$, the degree assumption forces $p(S)=0$, so its contribution to the left side is zero and the corresponding right-side term is nonnegative. Summing these inequalities over all subsets proves the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.noise_l2_fourier`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval`.
