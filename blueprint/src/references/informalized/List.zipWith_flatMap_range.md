<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.zipWith_flatMap_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zip of concatenated lists

**Claim.** When corresponding lists $f(z)$ and $f'(z)$ all have length $k$, applying $g$ entrywise to the two concatenations indexed below $n$ gives the concatenation of the entrywise zipped pairs for each index below $n$.

**Proof.** Proceed by induction on $n$. For $n=0$, both sides are empty. For the successor step, split each range into its first $n$ indices and its final index. FlatMap turns these into the concatenation of the earlier lists followed by the final list. The two earlier concatenations have equal lengths: each has length $nk$, by the fact that a flatMap over a range of $n$ lists of length $k$ has length $nk$ (`List.length_flatMap_range`). Consequently, zipping the two concatenations splits at the same boundary: the zip of the earlier portions is followed by the zip of the final lists. The induction hypothesis identifies the earlier portions with their per-index zips, and the final block supplies the remaining index, proving the result for $n+1$.

**Key facts.** `List.length_flatMap_range`.
