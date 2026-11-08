<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeIndex_key -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Round Trip on Tape Indices

**Claim.** For every one of the four work-tape indices, mapping it to its stack name and then back to a work-tape index returns the original index.

**Proof.** The four indices are handled in order: index $0$ maps through the main stack name back to $0$; index $1$ through the reverse stack name back to $1$; and index $2$ through the auxiliary stack name back to $2$. The remaining index is the unique final element of the four-element index type, and it maps through the stack stack name back to itself. Thus the two maps compose to the identity on all four indices.
