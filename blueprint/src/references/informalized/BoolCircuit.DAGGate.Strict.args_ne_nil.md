<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGGate.Strict.args_ne_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict gates have nonempty arguments

**Claim.** If a gate has pairwise distinct argument indices and its argument list has length one for a NOT gate and length two otherwise, then its argument list is nonempty.

**Proof.** Suppose instead that the argument list is empty. Its length is then zero, while the strictness condition says its length is either one or two according to the gate kind. Both possibilities contradict the empty list's length, so the argument list must be nonempty.
