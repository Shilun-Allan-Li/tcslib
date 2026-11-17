<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.entropy_message_le_complexity_mul_log_two_of_measure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transcript entropy bound

**Claim.** For a deterministic protocol for disjointness, the entropy of its transcript under any measure on the hard sample space is at most its communication complexity times $\log 2$.

**Proof.** The transcript takes values in the protocol's finite transcript space. The protocol's transcript-count bound says that this space has at most $2^c$ elements, where $c$ is the protocol's communication complexity (`card_transcript_le_two_pow_complexity`). The entropy bound for a finite-valued random variable supported on at most $2^c$ values then gives entropy at most $c\log 2$ (`entropy_le_nat_mul_log_two_of_card_le_two_pow`).

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.card_transcript_le_two_pow_complexity`, `ProbabilityTheory.entropy_le_nat_mul_log_two_of_card_le_two_pow`.
