<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.count_take_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counts in an indexed prefix

**Claim.** The number of occurrences of $a$ among the first $i$ values of the list of $f$ equals the number of indices $j<n$ such that $j<i$ and $f(j)=a$.

**Proof.** Proceed by induction on the domain size $n$, with the prefix length $i$ arbitrary. For $n=0$, both the list and the set of indices are empty. For the successor case, a zero-length prefix contributes neither entries nor indices. For a successor-length prefix, write the indexed list as its first value followed by the list on the remaining indices. The count in the prefix is the count in that tail prefix, plus one exactly when the first value is $a$. By the induction hypothesis, the tail count is the number of remaining indices below the prefix bound whose values equal $a$. The corresponding filtered index set splits into the first index and those remaining indices; its cardinality has the same decomposition. The two counts therefore agree.
