<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productSelectorPairPMF_eq_productRetention -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selector and retention pair laws

**Claim.** The law formed by independently sampling coordinatewise value pairs and selecting between each pair using correlated uniform signs of correlation $\theta$ equals the retention-and-resampling pair law with retention parameter $(1+\theta)/2$.

**Proof.** Write the selector-based sequence law as the product of its one-coordinate pair laws, transported from coordinate pairs to pairs of sequences by the coordinate regrouping equivalence. The one-coordinate selector law equals the one-coordinate retention-and-resampling law at parameter $\operatorname{selectorRetention}(\theta)$ (`selectorCoordinatePairPMF_eq_productRetention`). The parameter lies in $[0,1]$ by `selectorRetention_mem_Icc`, so the coordinatewise product representation applies: it identifies the product of these coordinate pair laws, after regrouping, with the retention-and-resampling pair law on sequences (`productRetentionPairPMF_eq_coordinateProduct`). Reversing that equality yields the stated identity.

**Key facts.** `FABL.selectorCoordinatePairPMF_eq_productRetention`, `FABL.selectorRetention_mem_Icc`, `FABL.productRetentionPairPMF_eq_coordinateProduct`.
