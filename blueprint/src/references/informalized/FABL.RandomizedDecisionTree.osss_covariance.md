<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.osss_covariance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# OSSS Covariance Inequality

**Claim.** For sign-valued functions $f$ and $g$ computed by the same randomized decision tree, their covariance is at most the sum over coordinates of the query probability for that coordinate times the influence of $g$ there.

**Proof.** For each seed, the corresponding deterministic tree computes $f$. The deterministic structural covariance inequality bounds $\operatorname{Cov}(f,g)$ by the sum of its structural query probabilities times the influences of $g$ (`FiniteDecisionTree.osss_covariance_structural`). Average this inequality over the seed law, using monotonicity of expectation. The left side is constant in the seed, so its average is still the same covariance. On the right, interchange the finite coordinate sum with expectation and pull each influence, which is constant in the seed, outside that expectation. The seed average of each structural query probability equals the randomized tree’s query probability (`RandomizedDecisionTree.queryProbability_eq_seed_structural`), giving the result.

**Key facts.** `FABL.FiniteDecisionTree.osss_covariance_structural`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_mul_const`, `FABL.RandomizedDecisionTree.queryProbability_eq_seed_structural`.
