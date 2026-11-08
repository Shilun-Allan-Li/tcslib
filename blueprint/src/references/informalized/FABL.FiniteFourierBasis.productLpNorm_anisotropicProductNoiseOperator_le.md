<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.productLpNorm_anisotropicProductNoiseOperator_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Anisotropic noise contracts $L^p$

**Claim.** If each noise parameter lies in $[0,1]$ and $p\geq1$, the anisotropic product noise operator does not increase the product-measure $L^p$ norm.

**Proof.** Because $p\geq1$, it is positive. For nonnegative numbers, raising both sides to the positive power $p$ preserves order, so it suffices to compare the $p$th powers of the norms. The norm identity \texttt{productLpNorm_rpow_eq_productMean_abs_rpow} rewrites these powers as the product means of the corresponding absolute values raised to $p$. The required inequality between those means is exactly the anisotropic noise moment bound (\texttt{productMean_abs_anisotropicNoise_rpow_le}). Taking the increasing $p$th root yields the asserted norm inequality.

**Key facts.** `FABL.productLpNorm_nonneg`, `FABL.productLpNorm_rpow_eq_productMean_abs_rpow`, `FABL.FiniteFourierBasis.productMean_abs_anisotropicNoise_rpow_le`.
