<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaRelevantCoordinateProgram_failureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Node decision failure bound

**Claim.** The probability that the low-degree junta program makes a bad decision at a restriction node is at most the prescribed failure parameter.

**Proof.** Let the bad event for the initial sample be that the sampled restriction batch is bad for the ideal node analysis. Since $P\subseteq J$ and $|J|\le k$, we have $|P|\le k$. The ideal batch bound gives probability at most half the failure parameter for this bad event. The restriction-sampling guarantee adds at most its own failure allowance, and the half-failure identity shows that the total source-bad probability is at most the full failure parameter. On every source-good sample, the continuation has zero probability of making a bad decision. The bind probability bound therefore gives total failure at most the source-bad probability plus zero, as required.

**Key facts.** `FABL.idealLowDegreeJuntaNodeBatchBadProbability_le`, `FABL.juntaRestrictionSampleProgram_badProbability_le`, `FABL.lowDegreeJuntaHalfFailure_value`, `FABL.lowDegreeJuntaNodeContinuation_badProbability_le_zero`, `FABL.LearningProgram.eventProbability_bind_le_add`, `FABL.positiveLearningParameter_toReal_mem_Ioc`.
