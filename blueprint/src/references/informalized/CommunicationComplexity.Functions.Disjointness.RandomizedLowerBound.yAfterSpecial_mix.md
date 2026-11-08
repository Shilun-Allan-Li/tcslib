<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_mix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mixing preserves the post-special profile

**Claim.** When two samples have the same special coordinate and agree on the indicated before-special and after-special profiles, the mixed sample has the same post-special profile as the second sample.

**Proof.** Fix a coordinate $i$. If $i$ is not strictly after the common special coordinate, both post-special vectors have value false there. If it is strictly after that coordinate, the bit of Bob in the mixed sample equals his bit in the second sample, by the definition of the mix and the fact that the two samples agree on their post-special profiles (the pointwise identity `yBit_mix`). Thus the vectors agree at every coordinate.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yBit_mix`.
