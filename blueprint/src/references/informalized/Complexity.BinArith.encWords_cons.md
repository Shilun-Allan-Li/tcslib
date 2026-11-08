<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.encWords_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a List of Bit Strings

**Claim.** For any bit string $w$ and any finite list $L$ of bit strings, encoding the list beginning with $w$ gives the pairing of $w$ with the encoding of the remaining list.

**Proof.** The encoding of a list beginning with $w$ is the pair encoding of $w$ with empty second component, concatenated with the encoding of the remaining list. The pair encoding identity that absorbs a following string into its second component (Complexity.BinArith.pairEncode_nil_append) rewrites this concatenation as the pair encoding of $w$ with the encoding of the remaining list.

**Key facts.** `Complexity.BinArith.pairEncode_nil_append`.
