<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_take_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Access within a truncated list

**Claim.** If $j<n$, then the entry at index $j$ in the first $n$ entries of $l$ equals the entry at index $j$ in $l$, with the same default value $d$.

**Proof.** An index strictly below $n$ is retained when the list is truncated to its first $n$ entries. Thus the optional entry at index $j$ is unchanged; applying the same default value to these equal optional entries gives the result.
