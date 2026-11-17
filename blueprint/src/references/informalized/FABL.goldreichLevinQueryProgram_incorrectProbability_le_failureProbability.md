<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinQueryProgram_incorrectProbability_le_failureProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Incorrectness Implies Estimate Failure

**Claim.** The probability that the Goldreich–Levin query program produces an incorrect state is at most the probability that its estimate trace contains an estimate with error at least $\tau^2/4$.

**Proof.** Consider the output law of the query program. For every outcome in its support that is incorrect, the support-to-correctness result says that an outcome whose trace has no failed estimate must be correct (\texttt{goldreichLevinQueryProgram\_correct\_of\_mem\_support\_of\_not\_hasFailure}). Taking the contrapositive, every supported incorrect outcome has a failed estimate. Thus the incorrect event, restricted to the support of the law, is contained in the estimate-failure event. Monotonicity of the law’s outer measure gives the same inequality for their outer probabilities. Both event probabilities are the real values of those outer probabilities; the estimate-failure outer probability is finite (\texttt{LearningProgram.outerEventProbability\_ne\_top}), so monotonicity of the real-value map yields the claimed inequality.

**Key facts.** `FABL.goldreichLevinQueryProgram_correct_of_mem_support_of_not_hasFailure`, `FABL.LearningProgram.outerEventProbability_ne_top`.
