<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.finiteUniformEmpiricalMean_juntaMatchObservation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical junta match frequency

**Claim.** The empirical mean of the indicator for matching the assignment on $P$ equals the number of matching sample inputs divided by the sample count.

**Proof.** The count of matching samples is the sum, over sample indices, of the indicator that the corresponding input matches the assignment (`FABL.juntaMatchCount_eq_sum`). After dividing by the sample count, this is exactly the empirical mean: at each index, the indicator is $1$ when the input matches and $0$ otherwise. The sample labels carried alongside the inputs do not affect this count.

**Key facts.** `FABL.juntaMatchCount_eq_sum`.
