<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.length_tableauBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tableau Block Length

**Claim.** For every $n$ and $t$, the list of tableau vertex indices for the snapshot coordinates at time $t$ has length equal to the number of possible snapshots of $M$.

**Proof.** The block maps the tableau-vertex function over the range of snapshot indices. Each index produces one vertex, so its length equals the length of that range, which is the snapshot count.
