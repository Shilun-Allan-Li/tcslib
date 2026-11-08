<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBlock_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Slice of an Encoded Snapshot

**Claim.** The two bits in the input-symbol slice of the encoded snapshot are exactly the two-bit encoding of the input symbol in the snapshot.

**Proof.** Fix either position in the two-bit slice. The input slice reads the encoded block at the offset for the state field plus that position. By the definition of the block encoding, this offset lies in its input-symbol component, where the stored bit is precisely the corresponding bit of the input symbol’s two-bit code. Since this holds at both positions, the two functions agree.
