<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingExercises.lean :: FABL.equalityPairStringTester_rejectionProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection probability for the pair tester

**Claim.** For positive $n$, the tester's rejection probability on a Boolean string is the fraction of pairs on which the two values differ.

**Proof.** The tester rejects exactly when its two queried values are unequal. Expanding the rejection probability as one minus the acceptance probability, and expressing the uniform seed distribution as a uniform expectation (`pmfExpectation_uniformPMF_eq_expect`), gives one minus the average indicator that the two values agree. The average of the constant function $1$ is $1$, so linearity of expectation rewrites this as the average of one minus that agreement indicator. For Boolean values, this difference is exactly the indicator that the values differ. The resulting expectation is the uniform fraction of disagreeing pairs. The transcript evaluation used here identifies each answer with the string value at its queried address (`NonadaptiveFunctionTester.transcript_apply`).

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
