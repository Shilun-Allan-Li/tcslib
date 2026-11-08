<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.TreeCircuit.toLayered_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finiteness of the layers

**Claim.** For every Boolean circuit $c$ on $n$ variables, each layer of its associated layered feedforward circuit has a finite set of nodes.

**Proof.** Apply the DAG-circuit finiteness theorem to the directed acyclic graph associated with $c$. It states that every layer of that circuit's layered form is finite; the tree-to-layered construction is this same layered form for the associated DAG circuit.

**Key facts.** `BoolCircuit.DAGCircuit.toLayered_finite`.
