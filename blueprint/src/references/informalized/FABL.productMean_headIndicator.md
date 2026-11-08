<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.productMean_headIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Biased Sign Indicator

**Claim.** For $0<p<1$ and either coordinate of two independent signs with probability $p$ of being $-1$, the mean of the indicator that the chosen coordinate is $-1$ is $p$.

**Proof.** Express the indicator on the two-coordinate product space as a product of coordinate factors: at the chosen coordinate use the indicator that the sign is $-1$, and at the other coordinate use the constant $1$. Independence makes the expectation of this product the product of the individual expectations (`pmfExpectation_independentProductPMF_prod`). The chosen coordinate contributes $p$ (`pmfExpectation_biasedSignPMF_negIndicator`), while the other contributes $1$ (`pmfExpectation_const_one`); therefore the mean is $p$.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_biasedSignPMF_negIndicator`, `FABL.pmfExpectation_const_one`.
