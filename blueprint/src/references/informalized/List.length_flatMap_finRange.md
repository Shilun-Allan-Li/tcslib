<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.length_flatMap_finRange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a flat-mapped finite range

**Claim.** If each list assigned to an index $i<n$ has length $k$, then concatenating those lists in index order has length $nk$.

**Proof.** The length of a concatenation of lists is the sum of their lengths. The finite range has $n$ indices, and each contributes length $k$, so the total is the sum of $n$ copies of $k$, namely $nk$.
