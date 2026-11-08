<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBlock_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Slice of an Encoded Snapshot

**Claim.** The first $B$ bits of the encoded snapshot are the code for the state in the snapshot.

**Proof.** Fix a position among the $B$ state bits. The state slice reads the encoded block at that same position, with the later input and work fields offset past it. By the definition of the block encoding, positions in this initial segment are supplied by the code for the snapshot’s state. Thus the state slice agrees with that code at every position.
