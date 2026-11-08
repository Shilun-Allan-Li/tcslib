<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.count_take_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting a Longer Prefix

**Claim.** For a finite list $l$, an element $x$, and $i<\operatorname{length}(l)$, the number of occurrences of $x$ among the first $i+1$ entries is the number among the first $i$ entries, plus one exactly when the entry at position $i$ is $x$.

**Proof.** Because $i$ is within the list, the prefix of length $i+1$ is the prefix of length $i$ followed by the single entry $l[i]$. The count of $x$ in a concatenation is the sum of its counts in the two parts, and its count in a singleton is one if that entry is $x$ and zero otherwise. Combining these facts gives the stated equality.
