<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecPort_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of codec ports

**Claim.** For every finite-state Turing machine $M$ with Boolean symbols, the codec has exactly $3k+7$ ports, where $k$ is its number of work tapes.

**Proof.** Replace the codec-port type by its proxy type through the given equivalence; equivalent finite types have the same cardinality. Counting the proxy constructors gives the fixed ports together with the indexed work-head ports, the two work-symbol ports for each tape, and the two summary ports. Their total simplifies to $3k+7$.
