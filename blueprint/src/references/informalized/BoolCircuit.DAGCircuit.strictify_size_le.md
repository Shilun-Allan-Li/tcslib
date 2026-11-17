<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.strictify_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for strictification

**Claim.** The strictification of a circuit with positive input count has size at most four times its original size plus twelve.

**Proof.** Deconstantization increases circuit size by three (`DAGCircuit.deconst_size`). The sealing bound applied to the deconstantized circuit gives a strictification size at most four times that enlarged size (`DAGCircuit.seal_size_le`). Substituting the increase yields $4(\mathrm{size}(C)+3)=4\,\mathrm{size}(C)+12$, as claimed.

**Key facts.** `BoolCircuit.DAGCircuit.deconst_size`, `BoolCircuit.DAGCircuit.seal_size_le`.
