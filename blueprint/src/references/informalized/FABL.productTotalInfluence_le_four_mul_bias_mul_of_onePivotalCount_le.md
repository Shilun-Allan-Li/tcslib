<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.productTotalInfluence_le_four_mul_bias_mul_of_onePivotalCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence bound from pivotal count

**Claim.** For a monotone sign-valued function, if at every input at most $w$ coordinates are pivotal when the output is $+1$, then its total influence under the product law with bias parameter $p\in(0,1)$ is at most $4pw$.

**Proof.** For each coordinate, monotonicity identifies its influence with $4p$ times the probability that the coordinate is pivotal and the output is $+1$ (\texttt{productInfluence\_eq\_four\_mul\_bias\_mul\_onePivotalProbability\_of\_monotone}). Summing over coordinates and exchanging the sum with expectation expresses total influence as $4p$ times the expected number of positive-output pivotal coordinates (\texttt{sum\_biasedOutputPivotalProbability}). By hypothesis this count is at most $w$ at every input, so its expectation is at most $w$ (\texttt{pmfExpectation\_mono}, with constants integrating to themselves by \texttt{pmfExpectation\_const}). Since $p>0$, multiplying preserves the inequality and gives the bound $4pw$.

**Key facts.** `FABL.productInfluence_eq_four_mul_bias_mul_onePivotalProbability_of_monotone`, `FABL.sum_biasedOutputPivotalProbability`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
