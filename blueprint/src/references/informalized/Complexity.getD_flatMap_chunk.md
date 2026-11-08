<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.getD_flatMap_chunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing a fixed-length flat-map chunk

**Claim.** When every list $g(a)$ has length $c$, the entry at index $ci+j$ in the flat map of $l$, followed by $rest$, is the entry at index $j$ of $g(l_i)$, provided $i<|l|$ and $j<c$.

**Proof.** The fixed-length chunk decomposition (`Complexity.CfgTableau.take_drop_flatMap_append`) says that after dropping the first $ic$ entries from the concatenated flat map and remainder, the next $c$ entries are exactly $g(l_i)$. Apply indexing at position $j$ to this equality. Since $j<c$, taking those first $c$ entries does not alter the entry at position $j$; and dropping the prefix shifts the original index by $ic$. The given index is $ci+j$, equal to $ic+j$, so the two indexed entries agree, including their common default.

**Key facts.** `Complexity.CfgTableau.take_drop_flatMap_append`.
