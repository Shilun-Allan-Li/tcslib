<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BalancedSimulation.lean :: CommunicationComplexity.Deterministic.Protocol.numLeaves_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Leaf Count

**Claim.** Every deterministic communication protocol has a strictly positive number of leaves, and hence at least one leaf.

**Proof.** The protocol’s shape is a tree, and every tree has a strictly positive number of leaves. Applying this fact to the shape of the given protocol gives $0<\mathrm{numLeaves}(p)$.
