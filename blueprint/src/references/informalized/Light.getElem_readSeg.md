<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.getElem_readSeg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of a read segment

**Claim.** For an index $i$ within the read segment starting at $a$ and of length $n$, its entry is $\mu(a+i)$.

**Proof.** The segment is obtained by mapping $k\mapsto\mu(a+k)$ over the natural numbers from $0$ through $n-1$. At an in-range index $i$, the entry of this mapped range is the image of $i$ under that function, namely $\mu(a+i)$.
