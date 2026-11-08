<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGGate.eval_dedup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation invariant under deduplication

**Claim.** For an AND or OR gate, removing repeated indices from its input list leaves its evaluation unchanged.

**Proof.** Consider the two permitted gate kinds. For AND, the evaluation is true exactly when every listed index has a true lookup. Deduplication preserves which indices occur, so this condition is unchanged. For OR, the evaluation is true exactly when some listed index has a true lookup, which is likewise unchanged by removing repetitions. The NOT case is excluded by the hypothesis.
