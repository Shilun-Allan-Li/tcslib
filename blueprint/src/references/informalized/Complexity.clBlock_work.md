<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBlock_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Slice of an Encoded Snapshot

**Claim.** For each work tape, its two-bit slice in the encoded snapshot is exactly the two-bit encoding of the symbol on that tape in the snapshot.

**Proof.** Fix a tape and one of the two bit positions. The work slice addresses the work-field component after the state and input fields, at the position indexed by that tape and bit. In the block encoding, the work component decodes its position into the tape index by division by two and the within-tape bit by remainder modulo two. At the chosen position these are exactly the given tape and bit: the index identity follows from the quotient and remainder formula. Therefore the selected bit is the corresponding bit of that tape’s symbol code, at both positions.
