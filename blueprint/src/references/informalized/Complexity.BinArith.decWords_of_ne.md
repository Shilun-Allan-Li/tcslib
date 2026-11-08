<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.decWords_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoder Recursion on Nonempty Words

**Claim.** For every nonempty bit string $w$, its decoded list of words is the first projection of the pair parser applied to $w$, followed by the decoded list obtained from the second projection.

**Proof.** The decoder is defined by a conditional: it returns the empty list when its input is empty, and otherwise returns the first projection of the pair parse followed by the recursive decoding of the second projection. Since $w$ is nonempty, the second branch applies, giving the stated equality.
