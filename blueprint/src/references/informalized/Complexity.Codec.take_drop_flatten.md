<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.take_drop_flatten -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block extraction from a flattened list

**Claim.** If every list in a finite list of lists has length $w$, then for $j$ less than the number of lists, the length-$w$ block of the concatenation starting at position $wj$ is its $j$th list.

**Proof.** Induct on the list of blocks, allowing the index $j$ to vary. The empty list has no admissible index. For a nonempty list with first block $b$, if $j=0$, the first $w$ entries of the flattened list are exactly $b$, since $b$ has length $w$. If $j=j'+1$, remove the initial block $b$ from the flattened list. Because $|b|=w$, dropping $w(j'+1)$ entries is the same as first dropping $|b|$ entries and then dropping $wj'$. The desired block is therefore the $j'$th block of the remaining list, which is the induction hypothesis; the length assumption passes to every block in that tail.
