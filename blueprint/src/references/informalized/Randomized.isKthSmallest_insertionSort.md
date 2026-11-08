<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.isKthSmallest_insertionSort -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Kth Value of an Insertion Sort

**Claim.** If $1\le k\le |l|$, the element at zero-based position $k-1$ in the nondecreasing insertion sort of $l$ occurs in $l$, has fewer than $k$ entries strictly below it, and has at least $k$ entries at most it.

**Proof.** Insertion sort produces a list that is a permutation of $l$ and is sorted in nondecreasing order. The sorted-list rank result (`Randomized.isKthSmallest_of_sorted`) says that the entry at position $k-1$ in such a list satisfies the defining conditions for being the $k$th smallest value, provided $1\le k$ and that position is within the list. Here insertion sort preserves length, and $k\le |l|$ ensures that $k-1$ is a valid position. Applying the rank result gives the claim.

**Key facts.** `Randomized.isKthSmallest_of_sorted`.
