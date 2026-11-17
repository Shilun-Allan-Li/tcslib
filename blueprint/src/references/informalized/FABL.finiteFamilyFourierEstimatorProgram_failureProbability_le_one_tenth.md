<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyFourierEstimatorProgram_failureProbability_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator failure probability bound

**Claim.** Under the stated Fourier concentration assumption, the estimator program's probability of producing a hypothesis whose relative Hamming distance from the target exceeds $\varepsilon$ is at most $1/10$.

**Proof.** Rewrite the event probability using the program's run law, which identifies the estimator program with the random-matrix output law (`runWithCost_finiteFamilyFourierEstimatorProgram`). The output-law measure formula (`randomExampleMatrixOutputLaw_toOuterMeasure_apply`) then expresses the probability of failure as the measure of the set of input matrices whose estimator output has error greater than $\varepsilon$. The preimage in this formula is exactly that failure event. Since a probability mass function's measure agrees with its outer measure on this event, the desired probability is the measure of the failure set under the input-matrix law. The Fourier concentration hypothesis and the estimator's analysis bound this measure by $1/10$ (`measure_finiteFamilyFourierEstimatorOutput_failure_le_one_tenth`).

**Key facts.** `FABL.runWithCost_finiteFamilyFourierEstimatorProgram`, `FABL.LearningProgram.randomExampleMatrixOutputLaw_toOuterMeasure_apply`, `FABL.measure_finiteFamilyFourierEstimatorOutput_failure_le_one_tenth`.
