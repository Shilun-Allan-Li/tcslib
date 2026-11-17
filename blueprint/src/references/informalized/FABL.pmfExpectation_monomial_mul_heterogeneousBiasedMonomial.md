<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_monomial_mul_heterogeneousBiasedMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mixed biased monomial expectation

**Claim.** For independent signs with coordinate biases determined by $p_i$, the expectation of the ordinary monomial on $T$ times the standardized biased monomial on $S$ is $\left(\prod_{i\in S}2\sqrt{p_i(1-p_i)}\right)\left(\prod_{i\in T\setminus S}(1-2p_i)\right)$ if $S\subseteq T$, and is zero otherwise.

**Proof.** Rewrite the product of monomials as a product over coordinates: coordinate $i$ contributes the sign if $i\in T$, the standardized biased sign if $i\in S$, and the corresponding factor is omitted when the index is absent (`FABL.monomial_mul_heterogeneousBiasedMonomial`). Independence factors the expectation of this coordinate product into the product of its one-coordinate expectations (`FABL.pmfExpectation_independentProductPMF_prod`). For each coordinate, there are four cases. If $i$ lies in both sets, the expected sign times standardized sign is the standard deviation scale. If it lies in $S$ only, the standardized sign has mean zero. If it lies in $T$ only, the sign has mean $1-2p_i$. If it lies in neither, the factor is constantly one and has expectation one. These are the coordinate expectation identities `FABL.pmfExpectation_biasedSignPMF_sign_mul_standardized`, `FABL.pmfExpectation_biasedStandardizedSign`, `FABL.pmfExpectation_biasedSignPMF_signValue`, and `FABL.pmfExpectation_const_one`, respectively. If $S\subseteq T$, every coordinate in $S$ is in the overlap, every coordinate in $T\setminus S$ contributes its bias mean, and all other coordinates contribute one. Multiplying these factors yields the stated formula. If $S\nsubseteq T$, choose $i\in S\setminus T$. Its coordinate factor is zero, so the entire product, and hence the expectation, is zero.

**Key facts.** `FABL.monomial_mul_heterogeneousBiasedMonomial`, `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_biasedSignPMF_sign_mul_standardized`, `FABL.pmfExpectation_biasedStandardizedSign`, `FABL.pmfExpectation_biasedSignPMF_signValue`, `FABL.pmfExpectation_const_one`.
