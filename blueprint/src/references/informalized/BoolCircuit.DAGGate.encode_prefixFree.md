<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.DAGGate.encode_prefixFree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix freeness of gate encoding

**Claim.** If the encoding of a gate followed by a Boolean list equals the encoding of another gate followed by a Boolean list, then the gates are equal and the trailing lists are equal.

**Proof.** Write each gate as its kind together with its argument list. The encoding concatenates the kind encoding with the encoding of the arguments. Prefix freeness of the kind encoding first identifies the two kinds and leaves an equality between the argument encodings followed by their respective tails (`GateKind.encode_prefixFree`). The argument-list encoding is prefix-free whenever its element encoding is prefix-free (`encodeList_prefixFree`). Since the natural-number encoding is prefix-free (`encodeNat_prefixFree`), this identifies the argument lists and the tails. Thus the gates and the trailing Boolean lists agree.

**Key facts.** `BoolCircuit.GateKind.encode_prefixFree`, `BoolCircuit.encodeList_prefixFree`, `BoolCircuit.encodeNat_prefixFree`.
