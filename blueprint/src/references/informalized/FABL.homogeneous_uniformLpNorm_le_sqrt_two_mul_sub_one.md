<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.homogeneous_uniformLpNorm_le_sqrt_two_mul_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching improvement implies the square-root bound

**Claim.** A Fourier-homogeneous function of degree $k$ satisfies $\|f\|_{2r}\le \sqrt{2r-1}^{\,k}\|f\|_2$.

**Proof.** The matching-improvement estimate (FABL.homogeneous_uniformLpNorm_le_matchingImprovement) bounds the norm by the product of the matching improvement constant and $\sqrt{2r-1}^{\,k}\|f\|_2$. The constant is at most $1$ (FABL.matchingImprovementConstant_le_one). The remaining factor is nonnegative, since the square root, its integer power, and the norm are nonnegative (FABL.uniformLpNorm_nonneg). Replacing the improvement constant by $1$ therefore proves the claim.

**Key facts.** `FABL.homogeneous_uniformLpNorm_le_matchingImprovement`, `FABL.matchingImprovementConstant_le_one`, `FABL.uniformLpNorm_nonneg`.
