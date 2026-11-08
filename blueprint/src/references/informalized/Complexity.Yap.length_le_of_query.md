<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.length_le_of_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Length Bound

**Claim.** If the pair encoding of data $d$ and query $q$ is accepted by the Boolean circuit value language, then $|q|\le |d|$.

**Proof.** Membership supplies a circuit $C$ and an input string $x$ such that the encoded pair is also the pair encoding of $C$ and $x$. Injectivity of pair encoding (`Turing.pairEncode_injective`) identifies the two components: $d=C.encode$ and $q=x$. The circuit has $|x|$ input bits, so its size is at least $|x|$. The size bound by encoding length (`BoolCircuit.DAGCircuit.size_le_length_encode`) then gives $|x|\le C.encode.length=|d|$, as required.

**Key facts.** `Turing.pairEncode_injective`, `BoolCircuit.DAGCircuit.size_le_length_encode`.
