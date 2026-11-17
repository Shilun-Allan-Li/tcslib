<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean :: CommunicationComplexity.Deterministic.OneWay.deterministic_communicationComplexity_le_of_oneWay_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-way bound implies interactive bound

**Claim.** If a function with finite nonempty output type has one-way deterministic communication complexity at most $n$, then its interactive deterministic communication complexity is at most $n+\lceil\log_2|\alpha|\rceil$.

**Proof.** By the characterization of one-way cost bounds (`communicationComplexity_le_iff`), choose a one-way protocol computing $f$ whose cost is at most $n$. Embed it into the finite-message model: Alice sends her one-way message, then Bob sends an index encoding the decoded output. The embedding preserves the computed output (`toFiniteMessage_run`) and has complexity equal to the original cost plus $\lceil\log_2|\alpha|\rceil$ (`toFiniteMessage_complexity`). The finite-message characterization of interactive complexity (`communicationComplexity_le_iff_finiteMessage`) therefore bounds the interactive complexity by this embedded protocol's complexity. Finally, adding the same output-encoding cost to the original cost bound gives at most $n+\lceil\log_2|\alpha|\rceil$.

**Key facts.** `CommunicationComplexity.Deterministic.OneWay.communicationComplexity_le_iff`, `CommunicationComplexity.Deterministic.communicationComplexity_le_iff_finiteMessage`.
