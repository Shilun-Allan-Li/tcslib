<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BalancedSimulation.lean :: CommunicationComplexity.Deterministic.Protocol.complexity_eq_zero_of_numLeaves_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-Leaf Protocols Have Zero Complexity

**Claim.** If a deterministic protocol has exactly one output node, then its communication complexity is zero.

**Proof.** If the protocol is an output node, its complexity is zero by definition. If it begins with an Alice message, its two continuation protocols each have at least one output node (`numLeaves_pos`). The root's leaf count is the sum of those two positive counts, so it is at least two, contradicting the assumption that it is one. The same argument rules out a Bob node. Therefore only the output case is possible.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.numLeaves_pos`.
