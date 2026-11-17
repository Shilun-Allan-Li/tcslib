<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_prepared -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepared Recorder Initialization

**Claim.** The configuration with the recorder's initial control, empty counter words and record, a clock of $T$ true bits, input $y$, and blank source work tapes is exactly the recorder encoding of the source machine's initial configuration on $y$, zero movement counts, empty record, and logical time zero.

**Proof.** Compare the two configurations component by component. Their control states and input-head positions agree: both use the recorder's initial state and the initial shifted input position. For the work tapes, split the tape indices into the counter region, the record buffer, and the remaining clock, input, and source-work-tape regions. In each region, the definitions give the same tape contents: empty counter words and record, $T$ true clock bits, input $y$, and blank source work tapes. The head positions likewise agree: all counter and source-work heads are at zero, the record head is at the empty record's end, and the clock is at logical time zero. Their output tapes are both empty. Thus every configuration field agrees.
