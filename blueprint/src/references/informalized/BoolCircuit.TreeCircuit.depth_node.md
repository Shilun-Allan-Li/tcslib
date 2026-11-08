<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.depth_node -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of a Circuit Node

**Claim.** A node with children $cs$ has depth one plus the maximum depth of its children, where the maximum for an empty list is zero.

**Proof.** Unfold the definitions: the depth of a node is one plus the right fold that takes the maximum of each child's depth and the accumulated value, starting from zero. That fold is exactly the maximum depth of the child list. Hence the node's depth is one plus that maximum.
