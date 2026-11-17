<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_filter_range_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup by Preceding Satisfying Indices

**Claim.** If $i<n$ and $q(i)$, then in the list of indices below $n$ satisfying $q$, the entry at position equal to the number of indices below $i$ satisfying $q$ is $i$.

**Proof.** Induct on $n$. The case $n=0$ is impossible under $i<n$. For the successor step, separate whether $i<n$ or $i=n$. In the first case, filtering the range through $n$ gives the filtered range below $n$ followed by the possible new index $n$. The count of indices satisfying $q$ below $i$ is at most the length of that earlier filtered list: the number satisfying $q$ strictly below $i$ is less than the count through $i$, because $q(i)$ holds, and the count through $i$ is at most the count through $n$ by monotonicity. Thus the requested position lies in the earlier list, and the induction hypothesis identifies its entry as $i$. In the second case $i=n$, the appended entry is retained because $q(n)$ holds; the number of satisfying indices below $n$ is exactly the length of the earlier filtered list. Lookup at that position in the concatenation therefore returns the appended entry $n$. The filtered-range length formula identifies that earlier length with the count below $n$.

**Key facts.** `List.length_filter_range`.
