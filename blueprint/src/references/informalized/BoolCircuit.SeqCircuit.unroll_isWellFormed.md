<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.unroll_isWellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formedness of the Unrolled Circuit

**Claim.** If every combinational gate has distinct inputs and every NOT gate has exactly one input, the same properties hold for every gate in the unrolling.

**Proof.** Take any gate in the unrolled list; it arises from some position $p$. By `unrollGate_cases`, either it has at most one input and is not a NOT gate, or it is a combinational gate whose original arguments have been mapped by the placement function. In the first case, a list of length at most one has no repeated entries, and the gate is not a NOT gate, so both required properties hold. In the second case, the original gate has distinct inputs by hypothesis. The placement function is injective (`place_injective`), so mapping its argument list preserves distinctness. Its gate kind is unchanged, and therefore any NOT gate still has exactly one input, as required.

**Key facts.** `BoolCircuit.SeqCircuit.unrollGate_cases`, `BoolCircuit.SeqCircuit.place_injective`.
