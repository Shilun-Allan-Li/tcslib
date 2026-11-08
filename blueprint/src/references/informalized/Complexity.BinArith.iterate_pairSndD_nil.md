<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.iterate_pairSndD_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection iteration on the empty word

**Claim.** Applying the total second projection any natural number of times to the empty bit string gives the empty bit string.

**Proof.** The total second projection fixes the empty bit string. Iterating a function that fixes a point any number of times leaves that point unchanged, so every iterate of the projection sends the empty word to itself.
