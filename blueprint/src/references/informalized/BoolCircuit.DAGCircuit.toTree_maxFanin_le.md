<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.toTree_maxFanin_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin of the unfolded circuit

**Claim.** If every gate of a well-formed DAG circuit has at most $k$ input vertices, then the unfolded tree has maximum fanin at most $k$.

**Proof.** Apply the maximum-fanin bound for unfolding a vertex (`BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le`) to the output vertex. The hypothesis that every gate has at most $k$ arguments supplies the gate-size bound required by that lemma, and the output vertex is valid. The resulting unfolded tree is the circuit's tree unfolding, so its maximum fanin is at most $k$.

**Key facts.** `BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le`.
