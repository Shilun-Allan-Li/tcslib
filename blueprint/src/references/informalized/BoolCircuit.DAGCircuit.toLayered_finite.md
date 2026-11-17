<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.DAGCircuit.toLayered_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finiteness of the layered circuit

**Claim.** Every layer of the layered circuit associated to a well-formed DAG circuit on $n$ inputs has finitely many nodes.

**Proof.** Fix a layer index $d$. By definition, its node type is $	ext{Fin}(n+d)$ when $d$ is at most the number of gates, and otherwise it is the singleton type. A finite initial segment of the natural numbers is finite, and a singleton is finite. Thus the node type at every layer is finite, which is exactly the claimed finiteness of the layered circuit.
