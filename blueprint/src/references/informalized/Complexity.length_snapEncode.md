<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.length_snapEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snapshot Encoding Length

**Claim.** For every snapshot $s$ of $M$, its bit-string encoding has length equal to the number of possible snapshots of $M$.

**Proof.** The encoding is a list with one Boolean entry for each index in the finite index type whose size is the snapshot count. Every index contributes one entry, so the list length is exactly the number of possible snapshots.
