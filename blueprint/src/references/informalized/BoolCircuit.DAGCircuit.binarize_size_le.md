<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.binarize_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for binarization

**Claim.** The size of the binarized circuit is at most $n+|G|(|C|+2)$, where $G$ is the original gate list and $|C|=n+|G|$.

**Proof.** The rewrite length bound (`DAGCircuit.rewrite_length_le`) bounds the number of gates after rewriting by the sum, over the original gates, of each gate's argument count plus two. Each original gate has at most $|C|$ arguments (`DAGCircuit.args_length_le_size`), so this sum is at most $|G|(|C|+2)` (`DAGCircuit.sum_cost_le`). Adding the unchanged $n$ input vertices gives the claimed size bound.

**Key facts.** `BoolCircuit.DAGCircuit.args_length_le_size`, `BoolCircuit.DAGCircuit.rewrite_length_le`, `BoolCircuit.DAGCircuit.sum_cost_le`.
