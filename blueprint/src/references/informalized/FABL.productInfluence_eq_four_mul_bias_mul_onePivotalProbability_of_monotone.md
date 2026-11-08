<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.productInfluence_eq_four_mul_bias_mul_onePivotalProbability_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence and Positive-Output Pivotal Probability

**Claim.** For $p\in(0,1)$ and a monotone Boolean function, the influence at coordinate $i$ equals $4p$ times the probability that the function outputs $+1$ and is pivotal at $i$.

**Proof.** The monotone pivotal identity states that the squared bias scale times the positive-output pivotal probability equals the mass of the output $+1$ times the influence (`sigma_sq_mul_biasedOutputPivotalProbability_eq_mass_mul_influence_of_monotone`). At output $+1$, that mass is $1-p$. Also, the squared bias scale is the bias variance, equal to $4p(1-p)$ (`biasSigma_sq`). Substituting these expressions into the identity gives $(1-p)$ times the influence equal to $4p(1-p)$ times the pivotal probability. Since $p<1$, the factor $1-p$ is nonzero and cancels, yielding the claimed formula.

**Key facts.** `FABL.sigma_sq_mul_biasedOutputPivotalProbability_eq_mass_mul_influence_of_monotone`, `FABL.biasSigma_sq`.
