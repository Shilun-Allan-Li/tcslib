<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.encWords_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding the Empty List

**Claim.** The encoding of the empty list of bit strings is the empty bit string.

**Proof.** The encoding is defined by flattening the pair encodings of the words in the list. For the empty list there are no words to contribute, so the flattened result is empty.
