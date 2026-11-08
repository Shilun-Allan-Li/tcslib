<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.toTree_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bound for unfolding a DAG

**Claim.** The depth of the tree obtained by unfolding a well-formed DAG circuit is at most the depth of the DAG circuit.

**Proof.** Apply the bound for unfolding a vertex (`BoolCircuit.DAGCircuit.unfoldVertex_depth_le`) to the output vertex, with fuel one greater than that vertex index and positive polarity. The output is a valid vertex, and its index is strictly less than this chosen fuel, so the lemma bounds the unfolded tree's depth by the circuit depth at the output. By definition, that latter quantity is the depth of the circuit, giving the claimed inequality.

**Key facts.** `BoolCircuit.DAGCircuit.unfoldVertex_depth_le`.
