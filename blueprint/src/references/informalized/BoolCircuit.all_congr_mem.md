<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.all_congr_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of List-Wide Boolean Tests

**Claim.** If two Boolean-valued functions agree on every entry of a list, then the tests that all entries satisfy the respective functions are equal.

**Proof.** Induct on the list. For the empty list, both tests are true. For a list with head $a$ and tail $l$, the test is the conjunction of the value at $a$ and the test on $l$. The hypothesis gives equality of the two values at $a`; it also restricts to the tail, so the induction hypothesis gives equality of the tail tests. The two conjunctions, and hence the list-wide tests, are equal.
