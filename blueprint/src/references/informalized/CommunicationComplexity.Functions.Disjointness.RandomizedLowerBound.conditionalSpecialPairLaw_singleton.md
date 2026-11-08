<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialPairLaw_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton mass of the pair law

**Claim.** The conditional law of the special-bit pair assigns to each singleton the same real mass as the fiber measure assigns to the event that the pair equals that value.

**Proof.** By definition, the conditional pair law is the pushforward of the fiber measure under the special-pair map. The mass of a singleton under a pushforward measure is the mass of its preimage; applying this to the singleton $\{b\}$ gives exactly the fiber event that the special pair equals $b$.
