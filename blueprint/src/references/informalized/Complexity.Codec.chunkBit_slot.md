<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.chunkBit_slot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State-Slot Bit

**Claim.** For a cell value and an index below the number of possible state-summary pairs, the chunk bit at that index is true exactly when the optional state-summary pair has that numerical code.

**Proof.** At an index below the number of possible state-summary pairs, the chunk encoding uses its state-slot clause: it tests whether the optional pair, mapped to its numerical code when present, equals the singleton containing the given index. Thus the bit is the Boolean decision of precisely the stated equality.
