<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily.lean :: BoolCircuit.KarpLipton.querySrcs_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Source Index Bound

**Claim.** For natural numbers $n,j,m$, every entry of the query source list is less than $n+j+2$.

**Proof.** Each entry comes from one of the list's displayed pieces. An index from the first piece is some $i<n$, so it is below $n+j+2$. The two explicit entries are $n+j$ and $n+j+1$. Each repeated entry is $n+j+1$, and each mapped entry from the final piece has the form $n+i$ with $i<j$, hence is below $n+j$. These cases exhaust membership in the concatenated list, and each gives the required strict bound.
