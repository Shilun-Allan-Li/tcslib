<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.exercise9_6_sum_le_inv_mul_norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted degree norms bound

**Claim.** For $0<\delta\le1$, the sum of the degree-part second norms weighted by $(1-\delta)^k$ is at most $\delta^{-1}\|f\|_2$.

**Proof.** Apply Cauchy–Schwarz to the finite sum, with weights $a_k=(1-\delta)^k$ and $b_k=\|f^{=k}\|_2$. This bounds the sum by $(\sum_k a_k^2)^{1/2}(\sum_k b_k^2)^{1/2}$. The geometric square-sum bound gives $\sum_k a_k^2\le1/\delta^2$ (`exercise9_6_geometric_square_sum_le`), hence its square root is at most $1/\delta$. For the other factor, each squared degree-part norm equals its Fourier weight (`fourierWeightAtLevel_eq_uniformLpNorm_degreePart_sq`). Summing those weights gives the sum of squared Fourier coefficients (`sum_fourierWeightAtLevel_range`); Parseval's identity identifies this with $\langle f,f\rangle_u$ (`plancherel`), which is $\|f\|_2^2$ (`uniformLpNorm_two_sq_eq_uniformInner`). Nonnegativity of the norm therefore makes the second square-root factor equal to $\|f\|_2$. Combining the two bounds proves the result.

**Key facts.** `FABL.exercise9_6_geometric_square_sum_le`, `FABL.fourierWeightAtLevel_eq_uniformLpNorm_degreePart`, `FABL.sum_fourierWeightAtLevel_range`, `FABL.plancherel`, `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.uniformLpNorm_nonneg`.
