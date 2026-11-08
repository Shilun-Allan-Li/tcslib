<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yVector_message_info_le_complexity_mul_log_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transcript information bound

**Claim.** For a deterministic protocol $p$, the conditional mutual information between Bob's input vector and the transcript given Alice's input vector, under the disjoint-conditioned hard distribution, is at most $\mathrm{complexity}(p)\log 2$.

**Proof.** Apply the conditional mutual information bound by the entropy of the right-hand variable, taking Bob's vector, the transcript, and Alice's vector as the three variables. Their measurability and finite-range hypotheses hold because these variables take values in finite discrete spaces. This gives that the desired conditional mutual information is at most the transcript entropy. The entropy bound for a protocol transcript under any measure then bounds that entropy by $\mathrm{complexity}(p)\log 2$. Chaining the two inequalities proves the result.

**Key facts.** `ProbabilityTheory.condMutualInfo_le_entropy_right`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.entropy_message_le_complexity_mul_log_two_of_measure`.
