<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.heterogeneousBiasedInfluence_eq_sigma_sq_mul_flipProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence and Flip Probability

**Claim.** For a Boolean-valued function, its heterogeneous biased influence at coordinate $i$ equals $\sigma_i^2$ times the probability that flipping coordinate $i$ changes its output.

**Proof.** Unfold the influence and flip-probability definitions. At each input $x$, the conditional variance of the real-valued Boolean function is $\sigma_i^2$ if flipping coordinate $i$ changes its output, and is zero otherwise; this is the pointwise identity supplied by `coordinateConditionalVariance_biasedSignPMF_toReal`. Substituting that identity into the expectation pulls the constant factor $\sigma_i^2$ outside, by linearity of finite probability expectation (`pmfExpectation_const_mul`).

**Key facts.** `FABL.coordinateConditionalVariance_biasedSignPMF_toReal`, `FABL.pmfExpectation_const_mul`.
