<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.getElem_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entry of the Gate List

**Claim.** At every index $j$ below the length of the constructed gate list, the entry is the gate assigned by the construction at index $j$.

**Proof.** The list is defined by mapping the gate assignment over the range of indices from $0$ up to the total number of gates. Its entry at any valid index is therefore the value of that assignment at the same index.
