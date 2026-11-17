<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.unfoldGate_maxFanin_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Fan-In After Unfolding

**Claim.** If a well-formed gate has at most $k$ arguments and each circuit assigned to one of its arguments has maximum fan-in at most $k$, then unfolding the gate at either polarity has maximum fan-in at most $k$.

**Proof.** Write the gate as its kind together with its argument list. For either an AND or an OR gate, unfolding forms a node whose children are the assigned circuits, one for each argument. The maximum fan-in of a node is the larger of its number of children and the largest maximum fan-in among those children (`TreeCircuit.maxFanin_node`). The number of children is the argument-list length, at most $k$. Each child has maximum fan-in at most $k$ by hypothesis; taking the maximum over the mapped list preserves this bound (`maxFaninL_map` and `foldr_max_le`). Thus the unfolded node has maximum fan-in at most $k`.

For a NOT gate, well-formedness requires exactly one argument. Its argument list is therefore a singleton, and unfolding returns the assigned circuit for that argument at the opposite polarity, rather than adding a new node. The hypothesis on assigned circuits gives the required bound directly.

**Key facts.** `BoolCircuit.TreeCircuit.maxFanin_node`, `BoolCircuit.maxFaninL_map`, `BoolCircuit.foldr_max_le`.
