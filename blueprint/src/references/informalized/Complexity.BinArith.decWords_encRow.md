<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.decWords_encRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Row

**Claim.** For every finite list $r$ of natural numbers, decoding the concatenation of the pair encodings of the binary bit lists of its entries, each with an empty second component, recovers the list of those binary bit lists.

**Proof.** By definition, $	ext{encRow}(r)$ is the encoding of the list obtained by applying the binary expansion map to each entry of $r$. The decoder recovers any encoded list of words: it reads each word from its pair encoding and continues with the remaining concatenation. Applying this to the list of binary expansions gives exactly the claimed list.
