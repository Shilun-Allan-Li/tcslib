<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncEquality.lean :: CommunicationComplexity.Functions.Equality.communicationComplexity_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Complexity of Equality at Zero

**Claim.** The deterministic communication complexity of equality on zero-bit inputs is $0$.

**Proof.** For the upper bound, use the protocol that outputs true immediately. There is only one zero-bit input on each side, so the two inputs are necessarily equal and this protocol computes equality. It has complexity zero. The characterization of complexity bounded by a natural number (`Deterministic.communicationComplexity_le_iff`) therefore gives an upper bound of zero. For the lower bound, communication complexity takes values in the extended naturals, whose least element is zero, so it is at least zero. The two bounds give equality.

**Key facts.** `CommunicationComplexity.Deterministic.communicationComplexity_le_iff`.
