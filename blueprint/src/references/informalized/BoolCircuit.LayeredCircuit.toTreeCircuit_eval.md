<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredCircuit.lean :: BoolCircuit.LayeredCircuit.toTreeCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Unrolled Tree

**Claim.** For every output node and Boolean input assignment, the tree circuit obtained by unrolling that node evaluates to the same value as the layered circuit at that node.

**Proof.** Unfold the definitions of the tree circuit at the output and of the layered circuit’s output evaluation. The resulting equality is the node-by-node evaluation correspondence (\texttt{BoolCircuit.nodeToTreeCircuit_eval}) at the final layer and the node representing the chosen output. That result says the tree produced by recursively unrolling any node evaluates to the value of that node in the layered circuit, so it gives the required equality.

**Key facts.** `BoolCircuit.nodeToTreeCircuit_eval`.
