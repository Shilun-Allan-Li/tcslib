<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.productMean_headIndicator_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Product of Sign Indicators

**Claim.** For $0<p<1$, the mean of the product of the two indicators that the respective independent signs are $-1$ is $p^2$.

**Proof.** Write the product of the two indicators as a product over the two coordinates, using at each coordinate the indicator that its sign is $-1$. The expectation of this coordinatewise product factors under the independent product distribution (`pmfExpectation_independentProductPMF_prod`). Each of the two factors has expectation $p$ (`pmfExpectation_biasedSignPMF_negIndicator`), so the mean is $p\cdot p=p^2$.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_biasedSignPMF_negIndicator`.
