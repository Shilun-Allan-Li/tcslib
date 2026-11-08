<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.length_flatMap_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a flattened range

**Claim.** If each list $f(z)$ has length $k$ for every $z<n$, then concatenating $f(0),\ldots,f(n-1)$ gives a list of length $nk$.

**Proof.** The length of a concatenation is the sum of the lengths of its component lists. Every element of `List.range n` is below $n$, so the hypothesis says that each corresponding list contributes length $k$. Summing over the $n$ elements of the range gives $nk$.
