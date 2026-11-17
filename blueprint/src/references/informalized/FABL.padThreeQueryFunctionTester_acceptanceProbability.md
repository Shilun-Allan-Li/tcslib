<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.padThreeQueryFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability under query padding

**Claim.** Adding a fourth, unused query position to a nonadaptive tester with three query positions leaves its acceptance probability on every function unchanged.

**Proof.** Acceptance probability is the expectation over the tester's seed of the indicator that the acceptance predicate accepts the transcript. The padded tester uses the same seed distribution. For each seed, its first three query positions are exactly the original queries, and its fourth position is unused. Its acceptance predicate feeds the original predicate the values at the first three positions. Consequently, the transcript supplied to the predicate agrees pointwise with the original transcript: at each original position its value is the queried function value, or no value when the query is absent (\texttt{NonadaptiveFunctionTester.transcript\_apply}). Thus the acceptance indicators agree for every seed, and their expectations, hence the acceptance probabilities, are equal.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
