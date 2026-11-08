<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.embedMap_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for Embedded Vertices

**Claim.** If the source list has length $m$ and all its entries are less than $L$, then every vertex $v<m+i$ maps to a vertex less than $L+i$.

**Proof.** Separate the cases $v<m$ and $v\ge m$. In the first case, the embedding map selects the $v$th source entry; the source-list bound guarantees that this entry is less than $L$ (the list has length $m$, so the default value is not used). Since $i$ is nonnegative, it is therefore less than $L+i$. In the second case, the map is $L+(v-m)$. From $v<m+i$ we get $v-m<i$, so this value is less than $L+i$.

**Key facts.** `BoolCircuit.getD_src_lt`.
