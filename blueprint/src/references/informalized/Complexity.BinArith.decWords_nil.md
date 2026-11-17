<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.decWords_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the Empty Word

**Claim.** The recursive decoder sends the empty bit string to the empty list of words.

**Proof.** At the empty input, the decoder's defining conditional takes its empty-word branch, whose value is the empty list.
