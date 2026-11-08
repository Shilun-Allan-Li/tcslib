<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.deMorgan_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for the De Morgan transformation

**Claim.** Writing $s=n+|G|$ for the size of the original circuit, the De Morgan transformed circuit has size at most $n+|G|(s+2)$.

**Proof.** The rewrite length bound (`DAGCircuit.rewrite_length_le`) bounds the number of transformed gates by the sum, over original gates, of each gate's argument count plus two. By the argument-length bound (`DAGCircuit.args_length_le_size`), each such count is at most $s$. The sum-cost bound (`DAGCircuit.sum_cost_le`) therefore makes the total at most $|G|(s+2)$. Adding the unchanged $n$ input vertices gives the asserted size bound.

**Key facts.** `BoolCircuit.DAGCircuit.args_length_le_size`, `BoolCircuit.DAGCircuit.rewrite_length_le`, `BoolCircuit.DAGCircuit.sum_cost_le`.
