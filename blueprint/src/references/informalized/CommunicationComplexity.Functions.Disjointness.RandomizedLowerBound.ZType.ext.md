<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZVariable.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.ZType.ext -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Achievable statistic extensionality

**Claim.** An achievable statistic is determined by its transcript, special coordinate, Alice-before vector, and Bob-after vector.

**Proof.** Achievable statistics are subtypes of raw statistics, so first compare their underlying raw statistics. The four assumed field equalities imply equality of those raw statistics by raw-statistic extensionality (`RawZType.ext`). Equality of the subtype elements then follows because their underlying values agree.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.RawZType.ext`.
