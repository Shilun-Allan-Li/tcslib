<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.maxFanin_le_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin bounded by circuit size

**Claim.** For every Boolean circuit $c$, its maximum fanin is at most its size.

**Proof.** Use structural induction on the circuit. A literal has maximum fanin $0$ and size $1$, so the claim holds. For a node with child list $cs$, the induction hypotheses give each child's fanin at most its size. The list bound `TreeCircuit.maxFaninL_le_sumSize` therefore bounds the children’s maximum fanin by the sum of their sizes. Also, `TreeCircuit.length_le_sumSize` bounds the number of children by that same sum. The node’s maximum fanin is the maximum of those two quantities (`TreeCircuit.maxFanin_node`), while its size is one plus the sum of the child sizes (`TreeCircuit.size_node`). These bounds imply that the maximum fanin is at most the node’s size.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.TreeCircuit.length_le_sumSize`, `BoolCircuit.TreeCircuit.maxFaninL_le_sumSize`, `BoolCircuit.TreeCircuit.maxFanin_node`, `BoolCircuit.TreeCircuit.size_node`.
