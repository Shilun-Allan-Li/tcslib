<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mix_mix_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Double Mixing Recovers the First Sample

**Claim.** If two samples have the same special coordinate, agree on Alice’s bits before it, and agree on Bob’s bits after it, then mixing them in both orders and mixing those results recovers the first sample.

**Proof.** After expanding the two mixtures, the special coordinate and special bits are those of the first sample. To compare the remaining coordinate data, fix a coordinate different from the common special coordinate. The Alice bit of a mixture comes from its first input (`xBit_mix`), so the Alice bit in the outer mixture agrees with that of $\omega_X$. The Bob bit comes from its second input (`yBit_mix`), so the Bob bit also agrees with that of $\omega_X$. Away from the special coordinate, these bits are the two bits of the coordinate stored in $\omega_X$ (`xBit_of_ne_special`, `yBit_of_ne_special`). A disjoint coordinate is uniquely recovered from its Alice and Bob bits (`coordinateOfBits_xBit_yBit`), so the stored coordinate agrees as well. Thus every field of the resulting sample equals the corresponding field of $\omega_X$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_mix`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yBit_mix`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_of_ne_special`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yBit_of_ne_special`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateOfBits_xBit_yBit`.
