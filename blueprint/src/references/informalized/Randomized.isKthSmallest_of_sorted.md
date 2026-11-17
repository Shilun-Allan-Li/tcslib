<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.isKthSmallest_of_sorted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rank of a Sorted Element

**Claim.** If a nondecreasing list $s$ is a permutation of $l$, and $1\le k$ with $k-1<|s|$, then the element at position $k-1$ occurs in $l$, fewer than $k$ entries of $l$ are strictly smaller than it, and at least $k$ entries are at most it.

**Proof.** Let $x=s[k-1]$. Since this position is valid, $x$ occurs in $s$, hence in $l$ because permutation preserves membership. Permutations also preserve predicate counts, so it suffices to count in $s$. At most the first $k-1$ entries can be strictly less than $x$: every later entry is at least $x$, by the nondecreasing order. Thus the number strictly below $x$ is at most $k-1$, hence is less than $k$. For the other inequality, every entry strictly below $x$ is among those first $k-1$ positions, so the first $k$ entries are all at most $x$. Equivalently, the number at most $x$ is the list length minus the number strictly above $x$; the sorted-order bound says that the latter is at most $|s|-1-(k-1)$. Therefore at least $k$ entries are at most $x$.

**Key facts.** `Randomized.countP_lt_getElem_le`, `Randomized.countP_getElem_lt_le`.
