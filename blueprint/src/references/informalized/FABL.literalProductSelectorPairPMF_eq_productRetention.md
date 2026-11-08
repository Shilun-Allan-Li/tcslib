<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.literalProductSelectorPairPMF_eq_productRetention -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selector pairs and product retention

**Claim.** The law formed by sampling two independent vectors from $\pi^{\otimes n}$ and applying correlated selector signs coordinatewise equals the law formed by sampling the first vector from $\pi^{\otimes n}$ and independently retaining each coordinate with probability $(1+\theta)/2$ or resampling it from $\pi$.

**Proof.** First, the literal construction of the selector pair has the same law as the product-selector construction, which samples independent one-coordinate selector pairs; this is the content of `literalProductSelectorPairPMF_eq_productSelectorPairPMF`. Next, the product-selector law equals the product-retention law by `productSelectorPairPMF_eq_productRetention`: in each coordinate, agreement of the two selector signs, which occurs with probability $(1+\theta)/2$, makes both outputs select the same one of the two sampled values, while disagreement makes the second output use the independently sampled value. The range fact `selectorRetention_mem_Icc` ensures this retention probability lies in $[0,1]$. Chaining these two equalities gives the claimed identity.

**Key facts.** `FABL.literalProductSelectorPairPMF_eq_productSelectorPairPMF`, `FABL.productSelectorPairPMF_eq_productRetention`, `FABL.selectorRetention_mem_Icc`.
