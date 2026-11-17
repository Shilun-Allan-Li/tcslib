<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton mass of Alice's special-bit law

**Claim.** The conditional law of Alice's special bit assigns to each singleton the same real mass as the fiber measure assigns to the event that Alice's special bit equals that value.

**Proof.** By definition, Alice's conditional law is the pushforward of the fiber measure under her special-bit map. The mass of a singleton under a pushforward is the mass of its preimage, which here is the event that Alice's special bit equals the specified value.
