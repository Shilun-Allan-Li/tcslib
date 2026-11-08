<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.productInfluence_dictator_one_quarter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of a One-Coordinate Dictator

**Claim.** On the one-dimensional sign cube, the dictator’s influence under bias parameter $1/4$ is $3/4$.

**Proof.** The biased influence formula expresses the influence as the square of the bias standard-deviation scale times the probability that flipping the chosen coordinate changes the function (`productInfluence_biased_eq_sigma_sq_mul_flipProbability`). For a dictator, flipping its sole input always changes its output, so this flip probability is $1$; the expectation of the constant function $1$ is $1$ (`pmfExpectation_const`). Thus the influence is $\mathrm{biasSigma}(1/4)^2$. The identity between the square of this scale and the bias variance (`biasSigma_sq`), followed by substituting $p=1/4$ into the variance formula, gives $3/4$.

**Key facts.** `FABL.productInfluence_biased_eq_sigma_sq_mul_flipProbability`, `FABL.pmfExpectation_const`, `FABL.biasSigma_sq`.
