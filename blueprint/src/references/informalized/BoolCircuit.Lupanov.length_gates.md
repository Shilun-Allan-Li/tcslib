<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.length_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Gate List

**Claim.** The constructed gate list has length $\mathrm{total}(n,k)$.

**Proof.** The list is obtained by mapping the gate assignment over the range of length $\mathrm{total}(n,k)$. Mapping preserves list length, so the constructed list has that length.
