<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaRestrictionSampleProgram_failureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure Probability of the Sampling Program

**Claim.** The probability that the junta restriction sampling program returns no batch is at most the failure parameter, provided |P| ≤ k.

**Proof.** Let R be the program's sample count and a the matching accuracy. The count is positive by `fourierEstimatorSampleCount_pos`. By `juntaRestrictionFailureSet_subset_empiricalBad`, failure to find M matching examples forces the empirical matching mean to differ from its expectation by at least a. The observation takes values in $[-1,1]$ by `juntaMatchObservation_mem_Icc`, so the finite-sample concentration bound `measure_finiteUniformEmpiricalMean_sub_expect_ge_le` bounds the probability of this deviation by $2\exp(-Ra^2/2)$. Since R is at least the Fourier estimator sample count, this is at most the same exponential expression with that count in place of R. The defining estimate `two_mul_exp_neg_fourierEstimatorSampleCount_le` bounds the latter by the failure parameter. Finally, `runWithCost_juntaRestrictionSampleProgram` identifies the program's run law with the uniform input law mapped to its extracted batch and a fixed cost. The preimage of the no-batch event is exactly the failure set, so the probability bound for that set is the desired program failure bound.

**Key facts.** `FABL.fourierEstimatorSampleCount_pos`, `FABL.juntaMatchObservation_mem_Icc`, `FABL.juntaRestrictionFailureSet_subset_empiricalBad`, `FABL.measure_finiteUniformEmpiricalMean_sub_expect_ge_le`, `FABL.two_mul_exp_neg_fourierEstimatorSampleCount_le`, `FABL.runWithCost_juntaRestrictionSampleProgram`.

**Caveat.** The supplied informal statement describes a different learning-theory task. This account follows the formal statement and proof source, which bound the probability of returning no batch.
