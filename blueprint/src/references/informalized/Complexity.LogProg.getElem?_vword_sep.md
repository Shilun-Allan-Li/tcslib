<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.getElem?_vword_sep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separators in an Encoded Bit Word

**Claim.** After the rendered $i$th segment of the virtual word, provided another segment follows, the next two entries are $0$ and $1$.

**Proof.** Induct on the segment list, generalizing $i$. A list with fewer than two segments cannot satisfy the hypothesis. With at least two segments and $i=0$, the virtual word begins with the first rendered segment followed by the separator $01$. Since the index in question is exactly the end of the first rendering, its next two entries are therefore false and true. For successor $i$, the segment at index $i+1$ in the list is the segment at index $i$ in its tail (`seg_cons_succ`), and its offset is the length of the first rendered segment plus the separator length plus the tail offset. Thus both queried positions lie past the initial block; indexing there reduces to the two corresponding positions in the tail, where the induction hypothesis supplies false and true. The zero-index identification is `seg_cons_zero`.

**Key facts.** `Complexity.LogProg.seg_cons_zero`, `Complexity.LogProg.seg_cons_succ`.
