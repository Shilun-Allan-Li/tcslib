<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.size_le_length_encodeCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit size and encoding length

**Claim.** For any natural number $n$ and Boolean circuit tree $C$ on $n$ variables, the size of $C$ is at most the length of its Boolean-list encoding.

**Proof.** Proceed by induction on the circuit tree. For a literal, its encoding contains a tag, its sign, and the unary encoding of its index, so its length is at least the literal's size, which is one. For a node with children $c_1,\ldots,c_m$, first establish by induction on a list of trees that the sum of their sizes is at most the length of the children encoding. The empty list has encoding $[\mathrm{false}]$, so its size sum, zero, is bounded by that length. For a nonempty list, the children encoding places a separator before the encoding of the first child and then appends the encoding of the remaining children; hence its length is at least one plus the first child's encoding length plus the remaining encoding length. The list induction hypothesis and the circuit induction hypotheses for each child bound the sum of child sizes by these lengths. Finally, the node encoding contributes its tag and gate label, in addition to the children encoding, while the node size is one plus the sum of child sizes. These contributions give the claimed bound.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.encodeChildren_nil`, `BoolCircuit.encodeChildren_cons`, `BoolCircuit.encodeCircuit_node`.
