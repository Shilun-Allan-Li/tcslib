<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.IsKthSmallest.isMedian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Rank Statistic Is a Median

**Claim.** An element whose rank is the specified middle rank has at least half the list entries at most it and at least half the entries at least it, counting repetitions.

**Proof.** Let $k=\lfloor(|l|+1)/2\rfloor+1$. The rank assumptions say that fewer than $k$ entries are strictly below $y$, and at least $k$ entries are at most $y$. The first inequality gives the needed lower bound on the number of entries at least $y$: the counts of entries strictly below $y$ and at least $y$ sum to $|l|$ (\texttt{countP\_lt\_add\_countP\_ge}), so the strict-below bound forces at least half the entries to be at least $y$. The second assumption gives at least $k$ entries at most $y$, which is enough for the corresponding half-list bound. These two bounds are exactly the stated median condition.

**Key facts.** `Randomized.countP_lt_add_countP_ge`.
