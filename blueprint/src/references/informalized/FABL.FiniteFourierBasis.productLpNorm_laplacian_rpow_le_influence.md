<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.productLpNorm_laplacian_rpow_le_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Laplacian norm bound by influence

**Claim.** For a sign-valued function and $1\leq p\leq2$, the $p$th power of the product-measure $L^p$ norm of its coordinate Laplacian is at most the coordinate influence.

**Proof.** Since $p\geq1$, it is positive. The identity \texttt{productLpNorm_rpow_eq_productMean_abs_rpow} converts the left side into the product mean of $|L_i f|^p$. The desired bound for that mean, under the sign-range hypothesis and $1\leq p\leq2$, is the moment estimate \texttt{productMean_abs_laplacian_rpow_le_influence}.

**Key facts.** `FABL.productLpNorm_rpow_eq_productMean_abs_rpow`, `FABL.FiniteFourierBasis.productMean_abs_laplacian_rpow_le_influence`.
