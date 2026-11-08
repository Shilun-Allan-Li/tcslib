<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.readCircuit_encodeCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoding and Decoding

**Claim.** For every Boolean circuit, fuel bound, and Boolean-list remainder, if the circuit encoding has length at most the fuel, reading that encoding followed by the remainder returns the circuit and leaves the remainder unread.

**Proof.** Proceed by structural induction on the circuit. For a literal, its encoding begins with the literal marker and sign, followed by the unary encoding of its variable index. Zero fuel is impossible because the encoding has positive length. With positive fuel, decoding the unary index recovers that index and leaves exactly the supplied remainder (`decodeNat_encodeNat`); the index bound holds because the literal already has an index in the variable range. Thus the reader returns the original literal and remainder.

For a node with connective bit $b$ and child list $cs$, its encoding has the form of the node marker and $b$, followed by the child-list encoding (`encodeCircuit_node`). Zero fuel is excluded by the length bound. With positive fuel, the node reader delegates to reading the children. The induction hypotheses provide the required decoding property for each child, and the encoded child-list length fits in the remaining fuel. The child-list decoding result (`readChildren_encodeChildren`) therefore returns exactly $cs$ and the original remainder, so the node reader reconstructs the original node.

**Key facts.** `BoolCircuit.TreeCircuit.ind`, `BoolCircuit.decodeNat_encodeNat`, `BoolCircuit.encodeCircuit_node`, `BoolCircuit.readChildren_encodeChildren`.
