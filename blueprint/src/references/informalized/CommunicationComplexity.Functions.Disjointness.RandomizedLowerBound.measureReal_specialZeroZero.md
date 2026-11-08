<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialZeroZero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Both Special Bits Vanish with Probability One Quarter

**Claim.** Under the uniform law on hard samples, the event that both special bits are false has probability $1/4$.

**Proof.** The event `specialZeroZero` is the instance of `specialBitsEvent` where both prescribed bits are false. The general result that every fixed pair of special-bit values has probability $1/4$ (`measureReal_specialBitsEvent`) therefore gives the desired probability directly.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialBitsEvent`.
