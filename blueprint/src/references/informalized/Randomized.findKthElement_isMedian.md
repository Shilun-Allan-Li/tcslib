<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.findKthElement_isMedian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Median output of randomized selection

**Claim.** For every outcome $(a,c)$ in the support of randomized selection at rank $\lfloor(|l|+1)/2\rfloor$ on a nonempty list $l$, there is a value $y$ with $a=y$ such that at least half the entries of $l$ are at most $y$ and at least half are at least $y$.

**Proof.** Since $l$ is nonempty, its length is positive, so the rank $k=(|l|+1)/2$ satisfies $1\le k\le |l|$. The correctness theorem for randomized selection says that every supported outcome at a valid rank has first coordinate $\mathrm{some}(y)$ for some $y$ that is the $k$th-smallest value in $l$ (`findKthElement_correct`). A $k$th-smallest value at this middle rank is a median: at least half the entries, counting multiplicity, are at most it and at least half are at least it (`IsKthSmallest.isMedian`). Taking this $y$ proves the claim.

**Key facts.** `Randomized.findKthElement_correct`, `Randomized.IsKthSmallest.isMedian`.
