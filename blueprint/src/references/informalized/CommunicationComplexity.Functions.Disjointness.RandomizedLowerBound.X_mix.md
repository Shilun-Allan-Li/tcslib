<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.X_mix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice's set under mixing

**Claim.** When two samples satisfy the stated agreement conditions, Alice's input set in their mixture equals Alice's input set in the first sample.

**Proof.** Fix a coordinate $i$. The bit identity for mixing (`xBit_mix`) says that Alice's bit at $i$ in the mixed sample is her bit at $i$ in the first sample. Membership in either input set is exactly the condition that this bit is true; hence the two sets have the same elements.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_mix`.
