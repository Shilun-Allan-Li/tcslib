<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.successCount_eq_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Success count and list count

**Claim.** For every $k$ and every Boolean-valued function $\omega$ on the first $k$ indices, the sum of the indicators of the indices where $\omega$ is true equals the number of true entries in its value list.

**Proof.** Proceed by induction on $k$. For $k=0$, both counts are zero. For the step from $k$ to $k+1$, separate the value at index $0$ from the remaining values. The sum splits into the indicator of $\omega(0)$ plus the sum over the shifted indices; the list of values is likewise the initial value followed by the list of shifted values. By induction, the latter sum equals the count of true entries in that tail. If the initial value is false, it contributes zero to both counts; if it is true, it contributes one to both. Thus the counts agree.
