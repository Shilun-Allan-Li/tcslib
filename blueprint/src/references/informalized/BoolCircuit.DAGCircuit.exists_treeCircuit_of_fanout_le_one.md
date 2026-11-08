<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.DAGCircuit.exists_treeCircuit_of_fanout_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tree representation under low fanout

**Claim.** If every gate vertex of a fanin two circuit has fanout at most one, the circuit has an equivalent Boolean circuit tree with maximum fanin at most two and size at most $3m+1$ and at most four times the circuit size, where $m$ is the number of gates.

**Proof.** Take the tree obtained by unfolding the circuit. The tree conversion evaluation theorem shows that it computes the same function, and the maximum-fanin theorem bounds its maximum fanin by two using the circuit's fanin bound. The low-fanout size theorem gives tree size at most $3m+1$. Finally, the circuit has size at least one because its output is a vertex among its inputs and gates. Combining this with the first size bound yields the stated bound by four times the circuit size.

**Key facts.** `BoolCircuit.DAGCircuit.toTree_size_le_of_fanout_le_one`, `BoolCircuit.DAGCircuit.toTree_eval`, `BoolCircuit.DAGCircuit.toTree_maxFanin_le`.
