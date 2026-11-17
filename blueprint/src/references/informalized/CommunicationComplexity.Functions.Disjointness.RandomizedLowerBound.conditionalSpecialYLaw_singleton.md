<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialYLaw_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton mass of the special-bit law

**Claim.** For any achievable summary value and bit $b$, the conditional law of Bob’s special bit assigns to the singleton $\{b\}$ the same mass as the fiber measure assigns to the event that the special bit equals $b$.

**Proof.** By definition, the conditional law is the pushforward of the fiber measure under the special-bit map. The measure of a singleton under this pushforward is, by the pushforward measure formula, the fiber measure of its preimage. That preimage is exactly the event that the special bit equals $b$, giving the claimed equality.
