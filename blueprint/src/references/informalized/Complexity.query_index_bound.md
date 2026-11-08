<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.query_index_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound from Binary Length

**Claim.** If the binary expansion of $r$ has length at most that of $n$, then $r\le 2n$.

**Proof.** The lengths of the binary expansions equal the corresponding natural-number sizes, so the hypothesis says $r.size\le n.size$. By the characterization of size, this implies $r<2^{n.size}$. If $n=0$, the size inequality forces $r=0$, and the result follows. Otherwise $n.size>0$, and the defining bound for the size gives $2^{n.size-1}\le n$. Therefore $2^{n.size}=2\cdot 2^{n.size-1}\le 2n$. Combining this with $r<2^{n.size}$ yields $r\le 2n$.
