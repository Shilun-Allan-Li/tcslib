<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.encWords_append_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending One Encoded Word

**Claim.** For every list $L$ of bit strings and every bit string $w$, encoding the list obtained by appending $w$ to $L$ gives the encoding of $L$ followed by the self-delimiting pair encoding of $w$ and the empty string.

**Proof.** Encoding a list is its flattening after each word is replaced by its pair encoding with empty second component. Flattening over a concatenation splits into the concatenation of the two flattened parts. Applying this to $L$ followed by the singleton list containing $w$ gives the encoding of $L$, followed by the pair encoding of $w$ with the empty string.
