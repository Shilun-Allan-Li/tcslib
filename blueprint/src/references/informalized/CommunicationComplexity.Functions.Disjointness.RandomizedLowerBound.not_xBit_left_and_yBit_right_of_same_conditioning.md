<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.not_xBit_left_and_yBit_right_of_same_conditioning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cross-Sample Disjointness

**Claim.** If two hard samples have the same special coordinate, agree on Alice’s bits before it, and agree on Bob’s bits after it, then away from that coordinate Alice’s bit in the first sample and Bob’s bit in the second cannot both be true.

**Proof.** Suppose toward a contradiction that both bits at $i$ are true. Split according to whether $i<T$. If $i<T$, the shared special coordinate implies that $i$ is also before the special coordinate in the second sample. Equality of the two preceding-bit vectors then forces Alice’s bit at $i$ to agree across the samples. Hence in the second sample both Alice’s and Bob’s bits at $i$ are true, contradicting the fact that within any one hard sample those two bits cannot both be true away from its special coordinate (\texttt{not_xBit_and_yBit_of_ne_special}). If $i<T$ fails, the assumption $i\ne T$ implies $T<i$. Now Bob’s following-bit vectors agree at $i$, so Bob’s bit also agrees across the samples. Both bits are therefore true at $i$ in the first sample, giving the same within-sample contradiction. These cases exhaust all coordinates distinct from $T$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.not_xBit_and_yBit_of_ne_special`.
