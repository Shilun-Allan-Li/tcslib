<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.pairFanin_xorNode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# XOR pair fanin bound

**Claim.** For any two input pairs of circuits, the maximum fanin of the two circuits produced by the XOR pair construction is at most the maximum of $2$ and the largest fanin among the four input circuits.

**Proof.** Each output circuit is an outer node with two children, each an inner node with two children. For any node, its maximum fanin is the maximum of its number of children and the largest maximum fanin among those children (the empty-list and cons formulas for list maximum fanin are `TreeCircuit.maxFaninL_nil` and `TreeCircuit.maxFaninL_cons`, and the node formula is `TreeCircuit.maxFanin_node`). Thus the outer nodes contribute fanin $2$, while each inner node has fanin bounded by the maximum of $2$ and the fanins of its two input circuits. Applying these formulas to both outputs gives the claimed bound.

**Key facts.** `BoolCircuit.TreeCircuit.maxFanin_node`, `BoolCircuit.TreeCircuit.maxFaninL_cons`, `BoolCircuit.TreeCircuit.maxFaninL_nil`.
