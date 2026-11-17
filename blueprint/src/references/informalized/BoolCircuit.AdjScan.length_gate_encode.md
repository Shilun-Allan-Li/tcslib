<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.length_gate_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate encoding length

**Claim.** For every Boolean circuit gate $g$, its encoding has length two plus the length of the list encoding of the natural-number encodings of its argument indices.

**Proof.** The encoding of a gate consists of the encoding of its kind followed by the encoding of its argument list. Each of the three possible gate kinds has an encoding of length two. Adding the argument-list encoding therefore gives the stated length.
