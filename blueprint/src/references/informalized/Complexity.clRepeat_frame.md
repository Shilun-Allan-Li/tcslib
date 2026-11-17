<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRepeat_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean-Call Configuration in the Clock Frame

**Claim.** Placing a source configuration in the repetition controller's source-tape slots, mapping its state to the lifted state, and retaining the unary clock tape gives exactly the controller configuration with that state word and clock cursor.

**Proof.** Compare the two configurations field by field. Their states agree: the placed source state is mapped to the right summand, giving the lifted state. Their input-head positions are both the initial position. For each work tape, split into the source slots and the extra clock slot. On a source slot, the placement selects the corresponding source tape, whose contents are the buffer encoding of that component of the state word and whose head is at zero; this is exactly how the controller configuration represents that tape. On the extra slot, the retained administrative tape is the buffer encoding of the unary word of length $N$, and its head is at $j$, as prescribed. Both outputs are empty. Hence all configuration fields agree.
