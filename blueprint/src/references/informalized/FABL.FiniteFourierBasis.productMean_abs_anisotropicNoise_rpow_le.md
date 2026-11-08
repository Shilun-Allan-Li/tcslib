<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.FiniteFourierBasis.productMean_abs_anisotropicNoise_rpow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Anisotropic noise contracts moments

**Claim.** For coordinate parameters $\rho_i\in[0,1]$ and $p\geq1$, the product mean of $|T_\rho f|^p$ is at most the product mean of $|f|^p$.

**Proof.** At each point, the anisotropic noise moment inequality bounds $|T_\rho f|^p$ by applying the same noise operator to the function $|f|^p$ (\texttt{abs_anisotropicProductNoiseOperator_rpow_le}). Taking product means preserves this pointwise inequality because expectation under a probability mass function is monotone (\texttt{pmfExpectation_mono}). Finally, the product mean is invariant under the anisotropic noise operator (\texttt{productMean_anisotropicProductNoiseOperator}), so the resulting upper bound is the product mean of $|f|^p$.

**Key facts.** `FABL.FiniteFourierBasis.abs_anisotropicProductNoiseOperator_rpow_le`, `FABL.pmfExpectation_mono`, `FABL.FiniteFourierBasis.productMean_anisotropicProductNoiseOperator`.
