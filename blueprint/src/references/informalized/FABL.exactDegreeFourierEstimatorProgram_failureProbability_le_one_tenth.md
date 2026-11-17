<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.exactDegreeFourierEstimatorProgram_failureProbability_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator failure probability bound

**Claim.** For a target whose Fourier degree is at most $k$, with $k\ge1$, the exact-degree estimator program's probability of outputting a Boolean function different from the target is at most $1/10$.

**Proof.** The program's run distribution is its random-example matrix output law. The outer-measure formula for that law (FABL.LearningProgram.randomExampleMatrixOutputLaw_toOuterMeasure_apply) converts the probability of an erroneous program outcome into the probability, under the input-matrix law, of the preimage of the error event. By the definitions of the program's output and the random-matrix outcome map, this preimage is exactly the event that the estimator output on the sampled inputs differs from the target. The input law is a probability measure, so its outer-measure value on this event agrees with its measure value. The resulting event is precisely the estimator failure event, whose measure is at most $1/10$ by the estimator failure bound (FABL.measure_exactDegreeFourierEstimatorOutput_failure_le_one_tenth).

**Key facts.** `FABL.runWithCost_exactDegreeFourierEstimatorProgram`, `FABL.LearningProgram.randomExampleMatrixOutputLaw_toOuterMeasure_apply`, `FABL.measure_exactDegreeFourierEstimatorOutput_failure_le_one_tenth`.

**Caveat.** The payload's informal prose describes a different learning-theory result; this account follows the formal statement and supplied proof.
