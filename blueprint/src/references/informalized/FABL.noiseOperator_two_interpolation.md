<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.noiseOperator_two_interpolation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpolation of the Second Norm

**Claim.** For $0\le\rho,\lambda\le1$, the second norm of the noise operator with parameter $\rho^{1-\lambda}$ is bounded by the geometric interpolation of the second norms at parameters $\rho$ and $1$.

**Proof.** The endpoint cases are handled first. If $\lambda=0$, the claimed inequality reduces to equality; if $\lambda=1$, the parameter is $1$, and the identity $T_1f=f$ (`noiseOperator_one`) gives equality. Now suppose $0<\lambda<1$. For each Fourier index $S$, set $w_S=\widehat f(S)^2$ and $a_S=(\rho^{|S|})^2$. These are nonnegative. The weighted geometric-sum inequality (`weighted_geometric_sum_le`) bounds $\sum_S w_S a_S^{1-\lambda}$ by $(\sum_S w_S)^\lambda(\sum_S w_Sa_S)^{1-\lambda}$. Parseval’s identity (`parseval`) and the second-norm-to-inner-product identity (`uniformLpNorm_two_sq_eq_uniformInner`) identify the left side with the square of the second norm of $T_{\rho^{1-\lambda}}f$: the coefficient formula (`fourierCoeff_noiseOperator`) supplies the multiplier, and the power identity (`noiseRpow_pow_sq`) rewrites its square as $a_S^{1-\lambda}$. The same identities identify the two sums on the right with the squares of the second norms of $f$ and $T_\rho f$. Finally, the identity for squaring real powers (`rpow_sq_eq_sq_rpow`) rewrites their product as the square of the desired right-hand side. Both sides before squaring are nonnegative (`uniformLpNorm_nonneg` and nonnegativity of real powers), so taking the order-preserving square root yields the result.

**Key facts.** `FABL.noiseOperator_one`, `FABL.weighted_geometric_sum_le`, `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.parseval`, `FABL.fourierCoeff_noiseOperator`, `FABL.noiseRpow_pow_sq`, `FABL.rpow_sq_eq_sq_rpow`, `FABL.uniformLpNorm_nonneg`.
