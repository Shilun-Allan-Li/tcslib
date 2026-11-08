<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productResamplingNoiseSensitivity_le_peres -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Peres bound for product resampling

**Claim.** For a product linear threshold function and $0<\delta\le 1/2$, its product resampling noise sensitivity is at most $\sqrt{3/2}\,\sqrt{\delta}$.

**Proof.** 1. Put $\theta=1-2\delta$. The hypotheses on $\delta$ imply $\theta\in[-1,1]$, and the selector-retention probability at correlation parameter $\theta$ is $1-\delta$. The identity between the selector experiment and the product retention experiment (`literalProductSelectorPairPMF_eq_productRetention`) therefore identifies their joint laws, so their disagreement expectations agree.

2. Express the selector experiment by first drawing two independent product inputs, then drawing a correlated pair of Boolean selectors, and selecting the corresponding input at each coordinate. Fixing the two product inputs gives a Boolean-cube function obtained by composing the original threshold with this coordinatewise selection. The preservation result (`isLinearThreshold_selectProductInput`) says this is a linear threshold function.

3. Apply Peres's noise-sensitivity bound (`peresNoiseSensitivityBound`) to each such Boolean function at noise rate $\delta$. It bounds each conditional disagreement probability by $\sqrt{3/2}\,\sqrt{\delta}$. Averaging this pointwise bound over both product inputs preserves the inequality. The expectation of a constant is that constant (`pmfExpectation_const`), yielding the claimed bound.

**Key facts.** `FABL.one_sub_two_mul_mem_Icc`, `FABL.literalProductSelectorPairPMF_eq_productRetention`, `FABL.pmfExpectation_literalProductSelectorPairPMF`, `FABL.isLinearThreshold_selectProductInput`, `FABL.peresNoiseSensitivityBound`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
