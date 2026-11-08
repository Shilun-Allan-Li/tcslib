<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseBoolVector_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Vector Reversal

**Claim.** For every positive length, reversing a Boolean vector is injective: if two vectors have the same reversal, then they are equal.

**Proof.** Suppose vectors $v$ and $w$ have the same reversal. Apply reversal once more to both sides of that equality. Reversal applied twice returns each vector to itself (the involution identity, `reverseBoolVector_reverseBoolVector`), so the resulting equality is $v=w$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseBoolVector_reverseBoolVector`.
