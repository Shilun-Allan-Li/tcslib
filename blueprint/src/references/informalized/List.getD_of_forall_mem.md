<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_of_forall_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Predicate under defaulted lookup

**Claim.** If a predicate holds of the default and of every entry of a finite list, then it holds of the result of defaulted lookup at every index.

**Proof.** Split according to whether the index is within the list. In range, the lookup is an entry of the list, so the predicate follows from the assumption on every list entry. Out of range, lookup returns the default, where the predicate holds by hypothesis.
