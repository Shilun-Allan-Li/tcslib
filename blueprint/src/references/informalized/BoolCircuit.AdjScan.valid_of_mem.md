<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjScan.valid_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of Encoded Circuit Inputs

**Claim.** Every word in the language for a circuit family and task is valid for that task: size and type inputs have the required unary and canonical binary encoding, while edge inputs have the corresponding encoding with two canonical binary components.

**Proof.** Split according to the task. For a size query, membership supplies a unary length and an index whose encoding is the input; the index bound is irrelevant to validity. The binary word $\mathrm{Nat.bits}(i)$ is canonical (`canon_bits`), so these witnesses establish validity. The type-query case is identical: membership supplies the same encoded form, and the same canonicality fact applies. For an edge query, membership supplies the unary length and two indices encoded as a nested pair. Each component is a word of the form $\mathrm{Nat.bits}(i)$ or $\mathrm{Nat.bits}(j)$, hence both are canonical by `canon_bits`; the witnesses therefore establish pair validity.

**Key facts.** `Complexity.LogProg.canon_bits`.
