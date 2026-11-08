<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdjBasic.lean :: BoolCircuit.DAGCircuit.encode_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expanded Circuit Encoding

**Claim.** The encoding of $C$ is the concatenation of $n$ true bits followed by a false bit, the encoded gate list, and $C$'s output encoded as true bits followed by a false bit.

**Proof.** Expand the circuit encoding and the natural-number encoding. The latter is, by definition, a list of the specified number of true bits followed by one false bit. Applying this once to the input count and once to the output gives the displayed concatenation; the encoded gate list remains between them.
