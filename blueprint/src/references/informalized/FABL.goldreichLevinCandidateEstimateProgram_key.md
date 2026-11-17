<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinCandidateEstimateProgram_key -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate Estimate Record Key

**Claim.** Every outcome in the support of the candidate-estimation program run with inputs $\tau,J,P$ has a record whose coordinate set is $J$ and whose frequency prefix is $P$.

**Proof.** The program maps each estimator output to the record formed by adjoining the fixed fields $J$ and $P$. The law of the mapped program is the pushforward of the estimator's outcome law (`LearningProgram.runWithCost_map`). Membership in the support of a mapped probability distribution implies that the outcome comes from some supported input outcome under the mapping. Its record component therefore has the prescribed fields, so its key is $(J,P)$.

**Key facts.** `FABL.LearningProgram.runWithCost_map`.
