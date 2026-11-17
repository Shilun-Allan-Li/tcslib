<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xVector_message_info_le_complexity_mul_log_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Information Cost Bound

**Claim.** Under the hard distribution conditioned on disjoint inputs, the conditional mutual information between Alice’s input vector and the protocol transcript given Bob’s input vector is at most the protocol’s communication complexity multiplied by $\log 2$.

**Proof.** Conditional mutual information between Alice’s vector and the transcript given Bob’s vector is at most the entropy of the transcript (`ProbabilityTheory.condMutualInfo_le_entropy_right`). The transcript entropy is at most the protocol complexity times $\log 2$ (`entropy_message_le_complexity_mul_log_two_of_measure`). Chaining these two inequalities gives the claimed bound.

**Key facts.** `ProbabilityTheory.condMutualInfo_le_entropy_right`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.entropy_message_le_complexity_mul_log_two_of_measure`.
