<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredCircuit.lean :: BoolCircuit.LayeredCircuit.toTreeCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound for Tree Unrolling

**Claim.** If every gate has at most \(k\) inputs, then the tree circuit obtained by unrolling any output node has size at most \((k+1)^{\mathrm{depth}(F)}\).

**Proof.** Unfold the definition of the tree circuit at the chosen output. Apply the node-unrolling size bound (\texttt{BoolCircuit.nodeToTreeCircuit_size_le}) to that node in the final layer. It bounds the size of the unrolled tree at any layer \(m\) by \((k+1)^m\); taking \(m=\mathrm{depth}(F)\) gives the claim.

**Key facts.** `BoolCircuit.nodeToTreeCircuit_size_le`.
