<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily.lean :: BoolCircuit.KarpLipton.querySrcs_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Source Encoding

**Claim.** For bit strings $y$ and $p$ of lengths $n$ and $j$, respectively, mapping each query source index to the corresponding bit of $y\mathbin{++}p\mathbin{++}[0,1]$, with default $0$ out of range, yields the self-delimiting pairing of $y$ with $m-j$ copies of $1$, then $0$, then $p$.

**Proof.** Let $z=y\mathbin{++}p\mathbin{++}[0,1]$. For every $i<n$, its entry at index $i$ is the corresponding entry of $y$; for every $i<j$, its entry at index $n+i$ is the corresponding entry of $p$. The entries at indices $n+j$ and $n+j+1$ are $0$ and $1$, respectively. The length assumptions on $y$ and $p$ ensure these positions line up exactly in the concatenation. Mapping the first part of the query source list therefore duplicates each bit of $y$, producing the doubled string in the pairing. The next two indices contribute $0,1$; the repeated indices contribute $m-j$ copies of $1$; the following index contributes $0$; and the final indices, of the form $n+i$ for $i<j$, reproduce $p$. Concatenating these pieces gives the claimed pairing.
