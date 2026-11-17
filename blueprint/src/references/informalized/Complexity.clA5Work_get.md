<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Work_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing a Time-Major List

**Claim.** If $j<kN$, then entry $j$ of the concatenation, for each $t<N$ in order, of the lists $f(t,0),\ldots,f(t,k-1)$ is $f(\lfloor j/k\rfloor,j\bmod k)$.

**Proof.** Induct on $N$. For $N=0$, the hypothesis cannot hold. For the successor case, the stream consists of the first $N$ blocks followed by the block at time $N$, whose length is $k$. Its prefix has length $kN$. If $j<kN$, the desired entry lies in the prefix, and the induction hypothesis gives the formula. Otherwise, the entry lies in the final block. The bound $j<k(N+1)$ shows that its offset $j-kN$ is less than $k$. Consequently, division by $k$ gives quotient $N$ and remainder $j-kN$, so the entry in that block is $f(N,j-kN)$, which is the claimed value. (If $k=0$, the original strict bound is impossible.)
