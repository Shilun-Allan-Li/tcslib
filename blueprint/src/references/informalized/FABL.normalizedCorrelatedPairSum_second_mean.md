<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.normalizedCorrelatedPairSum_second_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Second Mean

**Claim.** For every $\rho\in[-1,1]$ and every natural number $n$, the expected second coordinate of the normalized correlated pair sum is zero.

**Proof.** The second coordinate of the normalized sum is $(\sqrt n)^{-1}\sum_{i=1}^n y_i$, where $y_i$ are the coordinates of the second sign vector (the identity `correlationSecondCoordinate_normalizedCorrelatedPairSum`). By the second-marginal identity for the correlated pair distribution (`pmfExpectation_correlatedPairPMF_snd`), its expectation is the expectation of the same normalized sum under a uniform sign vector. Uniform expectation agrees with Boolean-cube expectation (`pmfExpectation_uniformPMF_eq_expect`). Rewrite the normalized sum as the linear form with every coefficient $(\sqrt n)^{-1}$ (`normalizedMargin_eq_linearForm`). Linearity of expectation turns its expectation into the sum over coordinates of $(\sqrt n)^{-1}$ times the expectation of the corresponding coordinate sign. Each coordinate sign is the singleton monomial, whose expectation is zero by `expect_monomial`, since its index set is nonempty. Thus every summand vanishes, and so does the whole mean.

**Key facts.** `FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum`, `FABL.pmfExpectation_correlatedPairPMF_snd`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.normalizedMargin_eq_linearForm`, `FABL.expect_monomial`.
