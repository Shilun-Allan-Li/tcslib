<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.sum_take_map_range_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Partial Sums of a Mapped Range

**Claim.** When $j<n$, the sum of the first $j+1$ entries of the mapped range equals the sum of the first $j$ entries plus $f(j)$.

**Proof.** For any list in an additive monoid, extending the initial segment from length $j$ to length $j+1$ adds the entry at position $j$, using zero if that position is absent (`List.sum_take_succ_getD`). In the mapped range, the assumption $j<n$ ensures that position $j$ is present, and its value is $f(j)$ (`List.getD_map_range`). Substituting this value gives the formula.

**Key facts.** `List.sum_take_succ_getD`, `List.getD_map_range`.
