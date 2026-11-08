<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.productMean_abs_laplacian_rpow_le_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Laplacian moment bound

**Claim.** For a sign-valued function and $1\leq p\leq2$, the product mean of the $p$th power of the absolute coordinate Laplacian is at most the coordinate influence.

**Proof.** Rewrite the left side as the product mean of the conditional centered absolute $p$th moment using \texttt{productMean_abs_laplacian_rpow_eq_conditional}. Rewrite the influence as the product mean of the coordinate conditional variance using \texttt{productInfluence_eq_expect_coordinateConditionalVariance}. It remains to compare these conditional quantities pointwise. Fix all coordinates other than $i$ and regard the resulting section of $f$ as a function $g$ of coordinate $i$. It is still sign-valued. The one-coordinate estimate \texttt{pmfExpectation_abs_sub_mean_rpow_le_sq} says that for $1\leq p\leq2$, the expected $p$th power of its deviation from its mean is at most the expected square of that deviation, namely its variance. Averaging this pointwise inequality over the remaining coordinates, using monotonicity of expectation (\texttt{pmfExpectation_mono}), gives the claimed bound.

**Key facts.** `FABL.FiniteFourierBasis.productMean_abs_laplacian_rpow_eq_conditional`, `FABL.FiniteFourierBasis.productInfluence_eq_expect_coordinateConditionalVariance`, `FABL.pmfExpectation_abs_sub_mean_rpow_le_sq`, `FABL.pmfExpectation_mono`.
