<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin Bound for Unfolded Circuits

**Claim.** If each gate of $C$ has at most $k$ arguments, then unfolding any valid vertex with any fuel and polarity has maximum fanin at most $k$.

**Proof.** Induct on the fuel. At fuel zero the unfolding is a node with no children, so its maximum fanin is zero. With positive fuel, an input vertex unfolds to a literal, also with maximum fanin zero. Otherwise, the vertex corresponds to an actual gate (`BoolCircuit.DAGCircuit.getD_gates`). Every argument of that gate has smaller index than the vertex (`BoolCircuit.DAGCircuit.args_lt_vertex`), so the induction hypothesis bounds the maximum fanin of each argument's unfolding by $k$. The gate itself has at most $k$ arguments by assumption. The bound for unfolding a well-formed gate, given these two facts, yields maximum fanin at most $k$ (`BoolCircuit.unfoldGate_maxFanin_le`).

**Key facts.** `BoolCircuit.DAGCircuit.args_lt_vertex`, `BoolCircuit.DAGCircuit.getD_gates`, `BoolCircuit.unfoldGate_maxFanin_le`.
