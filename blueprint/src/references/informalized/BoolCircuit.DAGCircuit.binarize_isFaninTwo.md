<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.binarize_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in of the binarized circuit

**Claim.** After binarization, every gate still has pairwise distinct arguments, every negation gate has exactly one argument, and every gate has at most two arguments.

**Proof.** Apply the rewrite theorem that every gate produced by a correct rewrite satisfies its specified property (`DAGCircuit.rewrite_new_gates`). For binarization, that property is `FaninTwo`: well-formedness together with an argument list of length at most two. The rewrite construction supplies the required gadget correctness from the original circuit's well-formedness and the bound on each gate's argument count. Thus every gate of the binarized circuit has the stated three properties.

**Key facts.** `BoolCircuit.DAGCircuit.rewrite_new_gates`.
