<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigma.lean :: Complexity.Meyer.xbOf_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a bit from circuit encoding

**Claim.** For $j<|x|$, the membership bit for the encoded index description paired with $x$ in the language of well-formed fan-in-two Boolean circuits evaluating to true equals the $j$th bit of $x$.

**Proof.** First show that the encoded pair belongs to the circuit-value language exactly when $x_j$ is true. In the forward direction, membership supplies an input and a well-formed circuit witnessing the encoding. Decode the two parts of the pair: the second part is $x$, and equality of the first part with the index description, together with the circuit encoding theorem, identifies the witness circuit with the circuit that reads bit $j$. The encoded circuit’s output is therefore the $j$th bit, so its asserted true evaluation implies $x_j$ is true. In the reverse direction, use that index circuit itself as a witness. Its encoding is the required index description, it is well formed and fan-in two, and its evaluation on $x$ is true when $x_j$ is true. Finally, the defining membership bit is true precisely when membership holds. The established equivalence gives the claimed equality in both Boolean cases. The circuit-encoding uniqueness fact (BoolCircuit.DAGCircuit.eq_of_encode_eq), the index-circuit encoding fact (Complexity.Meyer.idxCircuit_encode), and the two pair-decoding facts (Complexity.pairFstD_pairEncode and Complexity.pairSndD_pairEncode) supply the identifications used above.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.Meyer.idxCircuit_encode`, `BoolCircuit.DAGCircuit.eq_of_encode_eq`.
