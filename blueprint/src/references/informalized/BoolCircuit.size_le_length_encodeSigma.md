<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.size_le_length_encodeSigma -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for paired encoding

**Claim.** For a Boolean circuit tree $C$ on $n$ variables, its size is at most the length of the concatenation of the unary encoding of $n$ and the Boolean-list encoding of $C$.

**Proof.** Write the paired object as its variable count $n$ together with its circuit $C$. The circuit encoding alone has length at least $C$'s size by the circuit-size encoding bound (BoolCircuit.size_le_length_encodeCircuit). The paired encoding appends this circuit encoding to the unary encoding of $n$, so its length is the sum of their lengths and is therefore at least the circuit encoding length. The claimed inequality follows.

**Key facts.** `BoolCircuit.size_le_length_encodeCircuit`.
