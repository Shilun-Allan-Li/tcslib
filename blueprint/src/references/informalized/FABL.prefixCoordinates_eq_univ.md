<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.prefixCoordinates_eq_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full prefix coordinates

**Claim.** If $n\le k$, then the coordinates in $\{0,\ldots,n-1\}$ whose indices are less than $k$ form the full coordinate set.

**Proof.** An element of the coordinate set has index less than $n$, and hence less than or equal to $k$; therefore its index is less than $k$. So every coordinate is retained by the filter. Conversely, the filtered set is formed from the full coordinate set and therefore contains no other elements. The two sets are equal.
