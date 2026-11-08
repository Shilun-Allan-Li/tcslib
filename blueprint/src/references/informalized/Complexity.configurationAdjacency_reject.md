<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationAdjacency_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection for Different Inputs

**Claim.** For distinct Boolean inputs of the same length, the adjacency formula evaluated on the concatenation of their configuration encodings is false.

**Proof.** Relabelling distributes over the concatenated input-equality and transition formulas, and evaluation of a concatenation of CNFs is conjunction. Since the encoded configurations come from distinct inputs, the input-equality formula evaluates to false by the rejection result for that formula (`configurationInputEquality_reject`). A conjunction with a false factor is false, regardless of the transition factor.

**Key facts.** `Complexity.configurationInputEquality_reject`.
