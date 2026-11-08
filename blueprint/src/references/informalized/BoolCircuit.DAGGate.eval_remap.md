<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGGate.eval_remap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under Input Remapping

**Claim.** If the remapped value at each input of a gate agrees with the original value at that input, then evaluating the remapped gate on the first value list agrees with evaluating the original gate on the second.

**Proof.** Write the gate as a kind together with its argument list. For each argument in that list, the hypothesis identifies the value read at its remapped index with the value read at the original index. Consequently, the conjunction of the values across the remapped argument list equals the conjunction across the original list, by the list conjunction congruence fact (`all_congr_mem`). The corresponding disjunctions are equal for the same reason (`any_congr_mem`). The gate evaluation is one of these two list operations, or the negation of the conjunction; in each case these equalities give the claimed equality of evaluations.

**Key facts.** `BoolCircuit.all_congr_mem`, `BoolCircuit.any_congr_mem`.
