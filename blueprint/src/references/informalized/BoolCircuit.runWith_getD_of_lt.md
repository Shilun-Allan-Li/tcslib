<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_getD_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Initial Values

**Claim.** At every index $j<|v|$, evaluating any finite gate list from $v$ leaves the value at $j$ equal to its initial value, with the same default convention.

**Proof.** The output list can be written as $v$ followed by some extension (`runWith_eq_append`). Since $j<|v|$, the list-indexing rule for an index within the left part of a concatenation says that reading this concatenated list at $j$ gives the value read from $v$ at $j$.

**Key facts.** `BoolCircuit.runWith_eq_append`.
