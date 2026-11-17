<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.matOfRows_lovaszRows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rows Encode the Sample Matrix

**Claim.** The matrix obtained from the rows of block values, reduced modulo $p$, equals the sample matrix masked by the adjacency matrix read from $w$.

**Proof.** Compare the two matrices entry by entry at indices $(i,j)$. The row construction selects the bit of $w$ at position $in+j$ and, when it is true, places the value of the length-$k$ block of $r$ starting at position $(ni+j)k$ in that entry; otherwise it places zero. The row-matrix conversion reduces this natural number modulo $p$. The sample matrix uses the same block value, cast into $\mathbb Z/p\mathbb Z$, and the masking matrix uses that same bit of $w$. The index identity for the pair-to-single-index equivalence is $\operatorname{index}(i,j)=j+ni$, so the block positions agree. If the bit is true both entries are the same reduced block value; if false both are zero. Hence all entries, and therefore the matrices, agree.
