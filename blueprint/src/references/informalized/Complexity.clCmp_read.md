<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Aligned Tape Reads

**Claim.** For any four Boolean words and any natural-number position $j$, the symbols read by the comparator's aligned work-tape heads are exactly the symbols at position $j$ in the respective words, with out-of-range positions read as blank.

**Proof.** In the specified configuration, every work-tape head is at position $j$, and tape $i$ stores the buffer representation of word $w_i$. Reading tape $i$ at that head therefore returns the word's symbol at position $j$, or no symbol when that position is beyond the word. This holds separately for each of the four tapes.
