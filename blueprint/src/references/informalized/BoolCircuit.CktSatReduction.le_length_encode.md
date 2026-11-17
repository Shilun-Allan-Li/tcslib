<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.le_length_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Length Bound

**Claim.** For every directed acyclic circuit $C$ with $n$ input vertices, the length of its bit-string encoding is at least $n$.

**Proof.** The encoding begins with the unary encoding of $n$, which consists of $n$ true bits followed by a false bit. Its length is therefore at least $n$. Since this initial block is a prefix of the full circuit encoding, the full encoding has length at least $n$.
