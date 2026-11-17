<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.seg_readSeg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a segment from a function

**Claim.** The values of $\mu$ starting at index $a$ agree, at every index in the list, with the list of the first $n$ values $\mu(a),\mu(a+1),\ldots,\mu(a+n-1)$.

**Proof.** The list is formed by mapping the function $i\mapsto\mu(a+i)$ over the indices from $0$ to $n-1$. At any valid index $i$ in that list, its entry is therefore $\mu(a+i)$ by the definition of the mapped range list. This is exactly the required segment agreement.
