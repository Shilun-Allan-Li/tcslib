<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.restrictCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Preservation Under Circuit Restriction

**Claim.** Restricting a circuit to the first $m$ variables while replacing out-of-range literals by constant gates preserves its size.

**Proof.** Induct on the circuit. A literal is replaced either by another literal or by a constant node; each has size one, so the size is unchanged. For a node, restriction retains the node and restricts each child. By induction each child's size is preserved. The node size is one plus the sum of its children's sizes, hence it too is preserved.

**Key facts.** `BoolCircuit.TreeCircuit.ind`.
