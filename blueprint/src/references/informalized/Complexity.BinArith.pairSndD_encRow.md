<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.pairSndD_encRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the Tail of an Encoded Row

**Claim.** For any finite list $r$ of natural numbers, the total second projection of its row encoding equals the encoding of the tail of $r$.

**Proof.** Proceed by cases on $r$. If $r$ is empty, both sides are empty by the definitions. If $r$ has a head followed by a tail, its row encoding is the word encoding of the head followed by the encodings of the tail's entries. The outer pair decoder removes the first encoded word and returns exactly that remaining concatenation, which is the row encoding of the tail.
