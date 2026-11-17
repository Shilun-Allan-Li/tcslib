<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.X_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Alice's input set

**Claim.** For any hard-distribution sample, Alice's input set in the dual sample is the coordinate reversal of Bob's input set in the original sample.

**Proof.** Fix a coordinate $i$. By the bit identity for the dual sample (`xBit_dualHardSample`), Alice's bit at $i$ in the dual sample equals Bob's bit at the reversed coordinate in the original sample. Thus $i$ belongs to the left-hand set exactly when its reversal belongs to the original Bob set. This is precisely membership in the reversed set, so the sets are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_dualHardSample`.
