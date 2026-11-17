<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.exactDegreeFourierEstimatorProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator program cost

**Claim.** Every supported outcome of the exact-degree Fourier estimation program has the stated cost: the family size times the samples per coefficient in random examples, zero queries, and that sample count plus the prescribed local work in total work.

**Proof.** The program's run distribution is the random-example matrix output law with the low-degree family as its index set, the prescribed sample count per index, and the stated local-work charge (FABL.runWithCost_exactDegreeFourierEstimatorProgram). Unfolding that law, membership in its support means the outcome is obtained from some sample-input matrix by the defining outcome map. That map assigns the cost $(|\mathcal F|m,0,|\mathcal F|m+\text{work})$ independently of the sampled matrix. Substituting the prescribed work gives the claimed cost.

**Key facts.** `FABL.runWithCost_exactDegreeFourierEstimatorProgram`.
