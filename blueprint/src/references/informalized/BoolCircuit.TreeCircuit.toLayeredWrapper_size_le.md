<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredCircuit.lean :: BoolCircuit.TreeCircuit.toLayeredWrapper_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound for the Circuit Embedding

**Claim.** For every Boolean circuit $C$ on $n$ variables, the number of non-input nodes in its feedforward circuit embedding is at most $\mathrm{size}(C)(\mathrm{depth}(C)+1)$.

**Proof.** The embedding has one non-input node in each of its positive layers, so its size is at most its depth. The tree size is at least one (`BoolCircuit.TreeCircuit.one_le_size`), and the depth plus one is positive. Multiplying the latter quantity by the tree size therefore gives a bound at least as large as the depth, which proves the claimed inequality.

**Key facts.** `BoolCircuit.TreeCircuit.one_le_size`.
