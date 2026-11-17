<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.length_encChunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a cell encoding

**Claim.** Every cell value has an encoding of length exactly $W$.

**Proof.** The cell encoding is formed by applying the finite-list constructor to a function indexed by the $W$ positions of the cell code. A list formed from a function on those positions has length equal to the size of its index set, hence the encoding has length $W$.
