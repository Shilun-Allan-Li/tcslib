<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.all_dedup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deduplication Preserves a List-Wide Test

**Claim.** For a list of natural numbers and a Boolean-valued function, the test that every entry satisfies the function is unchanged by removing repeated entries.

**Proof.** A list-wide Boolean test is true exactly when every member of the list satisfies the predicate. Deduplication preserves precisely which natural numbers occur: an entry belongs to the deduplicated list exactly when it belongs to the original list. Therefore the universal conditions on the two lists are equivalent, so their Boolean tests agree.
