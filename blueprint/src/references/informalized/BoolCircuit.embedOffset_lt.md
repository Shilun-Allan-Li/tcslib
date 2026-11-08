<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.embedOffset_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding Offset Bound

**Claim.** For every index $j$ in a list of circuits, the offset assigned to the $j$th circuit is less than the total embedding width of the list.

**Proof.** Induct on the circuit list, with the index allowed to vary. The empty list has no valid index. In a nonempty list, index zero has offset equal to the first circuit's gate count, which is less than that count plus one and the width of the remainder. For a successor index, the offset is the first circuit's gate count plus one, followed by the offset at the predecessor index in the remainder. The induction hypothesis bounds that latter offset by the remainder's width, giving the desired strict bound by adding the first circuit's contribution.
