<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.snapEncode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Snapshot Encoding

**Claim.** For every finite Turing machine $M$ over the Boolean alphabet, the encoding map from snapshots of $M$ to finite Boolean strings is injective.

**Proof.** Suppose snapshots $s$ and $s'$ have the same encoded Boolean string. Index that string by the finite index assigned to $s$ under the equivalence between snapshots and indices. At this coordinate, the encoding of $s$ has value true, since the index equals itself. Equality of the strings forces the encoding of $s'$ to have value true there as well, so its assigned index is the same. The equivalence is injective, hence $s=s'$.
