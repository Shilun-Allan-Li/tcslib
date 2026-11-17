<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_le_average_entropy_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice information complexity bound

**Claim.** For positive $n$, Alice’s information term is at most the protocol complexity times $\log 2$, divided by $n$.

**Proof.** First, the information term is bounded by the information that the full Alice input vector carries about the transcript conditioned on Bob’s input vector, divided by $n$ (`aliceInfoTerm_le_average_xVector_info`). The full-vector information is at most the protocol’s complexity times $\log 2$ (`xVector_message_info_le_complexity_mul_log_two`). Since $n$ is nonnegative, dividing this latter bound by $n$ preserves the inequality. Combining the two estimates gives the result.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_le_average_xVector_info`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xVector_message_info_le_complexity_mul_log_two`.
