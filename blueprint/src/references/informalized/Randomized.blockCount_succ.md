<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.blockCount_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Block Count

**Claim.** The number of the first $K+1$ consecutive length-$q$ blocks satisfying $B$ equals $1$ if the first length-$q$ prefix satisfies $B$, and $0$ otherwise, plus the number of the first $K$ consecutive length-$q$ blocks of the string obtained by dropping the first $q$ bits.

**Proof.** Unfold the definition as a count over the indices $0,\ldots,K$. The index $0$ contributes one exactly when the first length-$q$ prefix satisfies $B$. Reindex the remaining indices as successors of $i=0,\ldots,K-1$. The block beginning at position $(i+1)q$ is the length-$q$ prefix after first dropping $q$ bits and then dropping $iq$ more bits. Hence the remaining count is the block count of the dropped string, giving the formula.
