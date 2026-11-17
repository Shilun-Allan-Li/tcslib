<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.any_dedup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjunction is unchanged by deduplication

**Claim.** For a list of natural numbers, deduplicating the list does not change the disjunction of any Boolean-valued predicate over it.

**Proof.** A listwise disjunction is true exactly when some element of the list makes the predicate true. Deduplication preserves membership: an element occurs in the deduplicated list exactly when it occurs in the original list. Hence the existence of an element making the predicate true is the same for both lists, so their disjunctions agree.
