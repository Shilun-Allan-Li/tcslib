<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyFourierEstimatorProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator program exact cost

**Claim.** Every supported output-and-cost outcome of the estimator program has cost $(|\mathcal{F}|M,0,|\mathcal{F}|M+|\mathcal{F}|M(n+1))$, where $M$ is the prescribed number of samples per coefficient.

**Proof.** First rewrite the program's run law as the law obtained by mapping a uniformly sampled matrix of inputs to the estimator output and its cost. Membership in the support of this mapped law means that the outcome is the image of some sample-input matrix (`PMF.mem_support_map_iff`). Hence its cost is the cost assigned by that map: $|\mathcal{F}|M$ random examples, zero queries, and $|\mathcal{F}|M+|\mathcal{F}|M(n+1)$ work.

**Key facts.** `FABL.runWithCost_finiteFamilyFourierEstimatorProgram`.
