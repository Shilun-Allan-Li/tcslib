<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.faninTwo_embedGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in of an embedded circuit

**Claim.** If a circuit is well formed and every gate has at most two inputs, then every gate in its embedding has distinct inputs, every NOT gate has exactly one input, and every gate has at most two inputs.

**Proof.** Take a gate in the embedded list. It lies either in the mapped copy of an original gate or in the final singleton list. In the first case, write it as the deduplicated remapping of an original gate. The original gate has distinct arguments, and if it is a NOT gate then it has exactly one argument. Deduplication ensures the remapped arguments are distinct; it cannot increase their number, so the resulting gate still has at most two arguments. Remapping preserves the gate kind and the argument-list length before deduplication, so a NOT gate still has exactly one argument afterward. In the final singleton case, the gate is an AND gate with one argument, and hence has distinct arguments and fan-in one.
