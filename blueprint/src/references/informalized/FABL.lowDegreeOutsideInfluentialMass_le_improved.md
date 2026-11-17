<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.lowDegreeOutsideInfluentialMass_le_improved -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Improved low-degree mass bound

**Claim.** For positive $\eta$ and $\tau$, the low-degree Fourier mass on sets not contained in the coordinates whose influence is at least $\tau$ is at most $\rho^{-k}\tau^{1/(1+\eta)}I(f)$, where $\rho=\eta/(2+\eta)$ and $I(f)$ is the total influence of the real-valued sign representation.

**Proof.** Set $\rho=\eta/(2+\eta)$ and $b=1/(1+\eta)$. The hypotheses ensure $0<\rho\le1$. First bound the mass outside the influential coordinates by the sum of the low-degree coordinate masses over coordinates outside that set (`lowDegreeOutsideInfluentialMass_le_sum_coordinateMass`). For each such coordinate $i$, its influence is less than $\tau$ (`not_mem_influentialCoordinates`). The low-degree mass at $i$ is at most $\rho^{-k}$ times its $\rho$-stable influence (`lowDegreeCoordinateMass_le_inv_rho_pow_mul_stableInfluence`), and the improved stability estimate bounds that stable influence by $\tau^b$ times the Boolean influence at $i$ (`stableInfluence_improvedFriedgutRho_le`). Multiplying preserves the inequality because $\rho^{-k}\ge0$. Sum over these coordinates, then enlarge the sum to all coordinates: every added term is nonnegative, since $\rho^{-k}$ and $\tau^b$ are nonnegative and Boolean influence equals real-valued influence, which is nonnegative (`booleanInfluence_eq_influence_toReal`, `influence_nonneg`). Factoring out the common constants and recognizing total influence gives the result.

**Key facts.** `FABL.improvedFriedgutRho_pos`, `FABL.improvedFriedgutRho_le_one`, `FABL.lowDegreeOutsideInfluentialMass_le_sum_coordinateMass`, `FABL.not_mem_influentialCoordinates`, `FABL.lowDegreeCoordinateMass_le_inv_rho_pow_mul_stableInfluence`, `FABL.stableInfluence_improvedFriedgutRho_le`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`.
