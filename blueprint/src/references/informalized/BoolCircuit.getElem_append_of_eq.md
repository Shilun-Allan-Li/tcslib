<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.getElem_append_of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup in an appended list

**Claim.** If $i=|l_1|+j$ and $j$ is in range for $l_2$, then lookup at index $i$ in $l_1\mathbin{++}l_2$ is the entry at index $j$ of $l_2$.

**Proof.** Substitute the equality $i=|l_1|+j$. The standard indexing rule for an appended list says that an index at or beyond the length of the first list is redirected into the second list by subtracting that first length. Here the resulting index is $j$, which is valid by hypothesis, so the lookup is exactly $l_2[j]$.
