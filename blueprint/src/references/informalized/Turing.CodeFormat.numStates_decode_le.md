<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.numStates_decode_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded State Count Bound

**Claim.** For every bit string $\alpha$, the guard constant of $F$ times one more than the number of states of the code decoded from $\alpha$ is at most the maximum of the length of $\alpha$ and the length of the serialization of $F$'s fallback code.

**Proof.** Choose a state bound $n$, initial state $q$, and table $t$ assembling to the decoded code; such a representation exists by the surjectivity of assembly. Its state count is $n$. The serialization of this assembled code is the pair encoding of the binary representation of $n$ and the unary encoding of $q$ followed by the table bits. By the pair-encoding length formula (`length_pairEncode`), its length is twice the length of the binary prefix, plus the delimiter length, plus the length of that unary-and-table suffix. The table-length lower bound gives $F.\mathrm{guard}\,(n+1)\le |\mathrm{tableBits}(t)|$. Since the unary encoding and binary prefix contribute additional nonnegative lengths, this yields $F.\mathrm{guard}\,(n+1)\le |F.\mathrm{serialize}(F.\mathrm{decode}(\alpha))|$. The serialization-length bound for decoding (`serialize_decode_length_le`) then bounds this by $\max(|\alpha|,|F.\mathrm{serialize}(F.\mathrm{fallback})|)$, as required.

**Key facts.** `Turing.CodeFormat.serialize_decode_length_le`, `Turing.length_pairEncode`.
