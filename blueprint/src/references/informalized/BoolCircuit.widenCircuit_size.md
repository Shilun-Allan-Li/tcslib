<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.widenCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Preserved by Widening

**Claim.** Widening a circuit from $m$ variables to $n$ variables preserves its total number of nodes.

**Proof.** Induct on the circuit (`BoolCircuit.TreeCircuit.ind`). A literal remains a single literal after widening, so its size is unchanged. At a node, widening maps the operation over the children, while size is one plus the sum of the child sizes. By the induction hypotheses each widened child has the same size as before; therefore the sum, and hence the node's total size, is unchanged.

**Key facts.** `BoolCircuit.TreeCircuit.ind`.
