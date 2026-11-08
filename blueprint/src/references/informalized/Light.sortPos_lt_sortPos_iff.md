<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.sortPos_lt_sortPos_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of sorting order

**Claim.** For $i<N$ and $j<N$, the position of $i$ is strictly less than the position of $j$ exactly when $k(i)<k(j)$, or when their values are equal and $i<j$.

**Proof.** The implication from the value-and-index condition to the position inequality is the ordering theorem (`sortPos_lt_sortPos`). For the converse, suppose the position inequality holds. If the stated value-and-index condition failed, the natural-number order trichotomy gives either $i=j$, or the reverse ordering: $k(j)<k(i)$, or equal values with $j<i$. In the equality case $i=j$, the two positions are equal, contradicting the strict inequality. In either reverse-order case, apply `sortPos_lt_sortPos` with $j$ first; it says the position of $j$ is strictly less than that of $i$, also contradicting the assumed inequality. Thus the value-and-index condition must hold.

**Key facts.** `Light.sortPos_lt_sortPos`.
