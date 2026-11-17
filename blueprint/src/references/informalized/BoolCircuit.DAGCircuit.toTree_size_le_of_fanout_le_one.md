<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.DAGCircuit.toTree_size_le_of_fanout_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unfolded Size with Bounded Fanout

**Claim.** If $C$ is well formed, has at most two inputs per gate, and every non-input vertex is used by at most one gate, then its unfolded tree has size at most $3|C.\mathrm{gates}|+1$.

**Proof.** The size of the output tree is the unfolded size of the output vertex. If the output is an input vertex, its unfolded size is $1$, which is at most $3|C.\mathrm{gates}|+1$. Otherwise write the output as $n+k$, where $k$ is a gate index. The output belongs to the set of vertices introduced through gate $k$ (`BoolCircuit.DAGCircuit.rootSet_succ`). The sum of unfolded sizes over this set is at most $3(k+1)$ (`BoolCircuit.DAGCircuit.sum_rootSet_le`), using the fan-in and fan-out hypotheses. Since each summand is nonnegative, the output's unfolded size is at most that sum. Finally, $k+1\le |C.\mathrm{gates}|$, so the desired bound follows.

**Key facts.** `BoolCircuit.DAGCircuit.unfoldSize_input`, `BoolCircuit.DAGCircuit.rootSet_succ`, `BoolCircuit.DAGCircuit.sum_rootSet_le`.
