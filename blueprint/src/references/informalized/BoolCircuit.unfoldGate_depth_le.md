<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.unfoldGate_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Bound for Gate Unfolding

**Claim.** If every circuit assigned to an argument of a well-formed gate has depth at most $B$ at either polarity, then unfolding the gate at any polarity has depth at most $B+1$.

**Proof.** Write the gate as its kind and argument list. For either AND or OR, unfolding creates a node with one child for each argument. The depth of such a node is one plus the maximum depth of its children (`BoolCircuit.TreeCircuit.depth_node`); the maximum child depth is the maximum of the assigned depths (`BoolCircuit.maxDepth_map`). Since every listed argument has assigned depth at most $B$, their maximum is at most $B` (`BoolCircuit.foldr_max_le`), so the node has depth at most $B+1$. For a NOT gate, well-formedness forces exactly one argument $a$. Unfolding selects the assigned circuit at $a$ with reversed polarity, and its depth is at most $B$, hence certainly at most $B+1$.

**Key facts.** `BoolCircuit.TreeCircuit.depth_node`, `BoolCircuit.maxDepth_map`, `BoolCircuit.foldr_max_le`.
