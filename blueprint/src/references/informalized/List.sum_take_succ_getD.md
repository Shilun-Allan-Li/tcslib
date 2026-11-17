<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.sum_take_succ_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Partial Sums of a List

**Claim.** For a list in an additive monoid, the sum of its first $j+1$ terms is the sum of its first $j$ terms plus the entry at position $j$, interpreted as zero if that position is absent.

**Proof.** Split into whether $j$ is less than the list length. If it is, the first $j+1$ entries consist of the first $j$ entries followed by the entry at position $j$; adding their sums proves the formula. If $j$ is at least the length, both initial segments contain the whole list, while the default entry is zero, so the equality follows as well.
