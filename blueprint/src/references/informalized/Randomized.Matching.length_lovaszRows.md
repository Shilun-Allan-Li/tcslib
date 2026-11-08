<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.length_lovaszRows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimensions of the Lovász Rows

**Claim.** The list of rows constructed from $n,k,w,r$ has exactly $n$ rows, and each row has length $n$.

**Proof.** The outer list is obtained by mapping over the $n$ indices in the range from $0$ to $n-1$, so it has length $n$. For each such index, the row is itself formed by mapping over that same range of $n$ column indices; hence every row has length $n$. The values chosen in the conditional entries do not affect either length.
