<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.Y_mix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bob's set under mixing

**Claim.** When two samples satisfy the stated agreement conditions, Bob's input set in their mixture equals Bob's input set in the second sample.

**Proof.** Fix a coordinate $i$. The bit identity for mixing (`yBit_mix`) says that Bob's bit at $i$ in the mixed sample equals his bit at $i$ in the second sample. Each set contains $i$ exactly when the corresponding bit is true, so membership agrees at every coordinate and the sets are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yBit_mix`.
