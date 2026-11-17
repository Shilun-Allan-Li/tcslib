<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productSelectorPairPMF_retentionCorrelation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Retention parameter and selector correlation

**Claim.** For a retention parameter $\rho\in[0,1]$, the selector-based pair law with sign correlation $2\rho-1$ equals the retention-and-resampling pair law with retention parameter $\rho$.

**Proof.** The correlation $2\rho-1$ is in $[-1,1]$ (`retentionCorrelation_mem_Icc`), so the selector and retention pair-law identity applies with that correlation. It gives the retention parameter $\operatorname{selectorRetention}(2\rho-1)$. Since $\operatorname{selectorRetention}(\operatorname{retentionCorrelation}(\rho))=\rho$ (`selectorRetention_retentionCorrelation`), this is exactly the desired retention parameter, proving the result.

**Key facts.** `FABL.retentionCorrelation_mem_Icc`, `FABL.productSelectorPairPMF_eq_productRetention`, `FABL.selectorRetention_retentionCorrelation`.
