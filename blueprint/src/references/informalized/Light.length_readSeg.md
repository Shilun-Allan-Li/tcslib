<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.length_readSeg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read-segment length

**Claim.** For a function $\mu:\mathbb N\to\mathbb Z$ and natural numbers $a,n$, the list of values $\mu(a+i)$ for $i=0,\ldots,n-1$ has length $n$.

**Proof.** This list is the image of the length-$n$ range $[0,1,\ldots,n-1]$ under $i\mapsto\mu(a+i)$. Since mapping a function over a list preserves its length, the read segment has length $n$.
