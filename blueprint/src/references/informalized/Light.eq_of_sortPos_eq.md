<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.eq_of_sortPos_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of sorting position

**Claim.** If two indices below $N$ have the same sorting position, then the indices are equal.

**Proof.** For indices below $N$, the sorting-position comparison theorem says that one position is strictly smaller than another exactly when its key is smaller, or the keys agree and its index is earlier (`sortPos_lt_sortPos_iff`). If $i$ and $j$ have equal positions, neither position is strictly smaller than the other. The comparison criterion therefore rules out both that $kf(i)<kf(j)$ and that $kf(j)<kf(i)$. Their keys must be equal. With equal keys, it also rules out both $i<j$ and $j<i$, so the indices are equal.

**Key facts.** `Light.sortPos_lt_sortPos_iff`.
