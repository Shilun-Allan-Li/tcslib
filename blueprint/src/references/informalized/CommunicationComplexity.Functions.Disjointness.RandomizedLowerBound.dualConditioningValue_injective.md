<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualConditioningValue_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of conditioning duality

**Claim.** The coordinate-reversal duality map on triples is injective.

**Proof.** Suppose two triples have the same image under the duality map. Apply the duality map once more to both sides of that equality. Since applying it twice returns each triple to itself, the original triples are equal. Hence the map is injective.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualConditioningValue_dualConditioningValue`.
