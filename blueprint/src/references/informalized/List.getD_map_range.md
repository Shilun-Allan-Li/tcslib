<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_map_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing a mapped range

**Claim.** For $i<n$, the entry at position $i$ in the list obtained by mapping $f$ over $0,\ldots,n-1$ is $f(i)$.

**Proof.** The mapped range has length $n$, so the hypothesis $i<n$ makes its defaulted lookup equal to ordinary indexed access. The entry at index $i$ in the range mapped by $f$ is $f(i)$, as asserted.
