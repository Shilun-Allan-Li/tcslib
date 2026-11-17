<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily.lean :: BoolCircuit.KarpLipton.length_querySrcs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the query source list

**Claim.** For natural numbers $n,j,m$, the list of query sources has length $2n+2+(m-j)+1+j$, where $m-j$ denotes truncated subtraction.

**Proof.** The range from $0$ to $n-1$ contributes two entries for each of its $n$ indices, hence the flattened part has length $2n$. The next two-entry list contributes $2$, the replicated list contributes $m-j$, the following singleton contributes $1$, and mapping over the range of length $j$ contributes $j$. Length is additive under concatenation, so the total is $2n+2+(m-j)+1+j$.
