<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.length_elimRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Row Elimination

**Claim.** The elimination list has length equal to the minimum of the truncated lengths of the row and pivot list, each reduced by one.

**Proof.** By definition, elimination applies `zipWith` to the tails of the row and pivot list. The length of a `zipWith` result is the minimum of the two input lengths, while removing the head of a list leaves length one less, truncated at zero. Substituting these two tail lengths gives the claimed minimum.
