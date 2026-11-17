<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.pairDepth_xorNode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of the XOR Pair Construction

**Claim.** The maximum depth of the two circuits produced by the XOR pair construction is at most two plus the maximum depth among the four input circuits.

**Proof.** Each output is an OR node whose two children are AND nodes, so its depth is two plus the maximum of the depths of the four input circuits, with the relevant inputs distributed across the two branches. The depth formula for a node and the formula for the maximum depth of a nonempty list give these nested maxima (`BoolCircuit.TreeCircuit.depth_node`, `BoolCircuit.TreeCircuit.maxDepth_cons`, and `BoolCircuit.TreeCircuit.maxDepth_nil`). Comparing the resulting natural-number expressions yields the claimed bound.

**Key facts.** `BoolCircuit.TreeCircuit.depth_node`, `BoolCircuit.TreeCircuit.maxDepth_cons`, `BoolCircuit.TreeCircuit.maxDepth_nil`.
