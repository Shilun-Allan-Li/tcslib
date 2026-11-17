<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.productLaplacianL1_eq_influence_of_hasSignRange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The $L^1$ Laplacian equals influence

**Claim.** For a function taking values in $\{-1,1\}$, the product mean of the absolute coordinate Laplacian equals its coordinate influence.

**Proof.** First use invariance of the product mean under coordinate projection to replace the mean of $|L_i f|$ by the mean of its projection onto all coordinates except $i$. The projected absolute Laplacian is the conditional variance over coordinate $i$ for a sign-valued function (\texttt{coordinateProjection_abs_laplacian_eq_coordinateConditionalVariance}). Thus the expression is the product mean of that conditional variance. The influence equals this same mean by the identity expressing influence as expected coordinate conditional variance (\texttt{productInfluence_eq_expect_coordinateConditionalVariance}), proving the claim.

**Key facts.** `FABL.FiniteFourierBasis.productMean_projectOnCoordinates`, `FABL.coordinateProjection_abs_laplacian_eq_coordinateConditionalVariance`, `FABL.FiniteFourierBasis.productInfluence_eq_expect_coordinateConditionalVariance`.
