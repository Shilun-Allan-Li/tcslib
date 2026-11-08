<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.hasLogspaceAdjacency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace adjacency from uniformity

**Claim.** If a family of directed acyclic Boolean circuits is logspace-uniform, then it has polynomial size and its size, gate-type, and edge languages are all in LOGSPACE.

**Proof.** Choose a function $f$ witnessing logspace uniformity, together with the guarantee that on the unary input of length $n$ it outputs the encoding of the $n$th circuit. The polynomial size conclusion follows from the theorem that logspace-uniform circuit families have polynomial size (BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPolySize). For each task—size, a fixed gate type, or edges—the adjacency scan theorem says that the corresponding language is in LOGSPACE when supplied with this uniformity function and its logspace-computability bounds (BoolCircuit.AdjScan.lang_mem). Applying it to the size task, to each type task, and to the edge task gives all three language claims. These four conclusions are precisely logspace adjacency.

**Key facts.** `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPolySize`, `BoolCircuit.AdjScan.lang_mem`.
