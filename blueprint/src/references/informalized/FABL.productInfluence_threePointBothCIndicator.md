<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productInfluence_threePointBothCIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of the Two-Coordinate Indicator

**Claim.** For two independent uniform coordinates on the three-point set, the influence of the first coordinate on the indicator that both coordinates equal $c$ is $2/27$.

**Proof.** The Fourier formula for product influence expresses the influence in coordinate $0$ as the sum of squared Fourier coefficients over multi-indices whose coordinate-$0$ index is nonzero (`productInfluence_eq_sum_sq_fourierCoeff`). The coefficient table for the indicator identifies the coefficient at indices $(a_0,a_1)$ as the product of the one-coordinate coefficients at $a_0$ and $a_1$ (`threePointBothCIndicator_fourierCoeff_table`). Reindex the sum by pairs in $	ext{Fin }3\times\text{Fin }3$; the condition becomes $a_0\ne 0$. Substituting the three one-coordinate coefficient values and summing over the remaining index gives $2/27$, as claimed.

**Key facts.** `FABL.FiniteFourierBasis.productInfluence_eq_sum_sq_fourierCoeff`, `FABL.threePointBothCIndicator_fourierCoeff_table`.
