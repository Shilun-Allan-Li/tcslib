<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.getLastD_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final bit of a binary word

**Claim.** For every natural number $s$, the final entry of its binary bit list, using true as the default if the list is empty, is true.

**Proof.** If the bit list is empty, its last-entry operation with default true returns true directly. Otherwise, the last-entry operation returns the actual final bit, and the canonicality of the binary bit list (`canon_bits`) says that this bit is true.

**Key facts.** `Complexity.LogProg.canon_bits`.
