<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.productLpNorm_laplacian_rpow_le_two_rpow_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Laplacian norm bound with a factor of $2^p$

**Claim.** For a sign-valued function and $p\geq1$, the $p$th power of the product-measure $L^p$ norm of its coordinate Laplacian is at most $2^p$ times the coordinate influence.

**Proof.** The exponent $p$ is positive, so the norm-power identity \texttt{productLpNorm_rpow_eq_productMean_abs_rpow} identifies the left side with the product mean of $|L_i f|^p$. The required bound on this mean by $2^p$ times the influence is precisely the sign-valued Laplacian moment estimate \texttt{productMean_abs_laplacian_rpow_le_two_rpow_influence}.

**Key facts.** `FABL.productLpNorm_rpow_eq_productMean_abs_rpow`, `FABL.FiniteFourierBasis.productMean_abs_laplacian_rpow_le_two_rpow_influence`.
