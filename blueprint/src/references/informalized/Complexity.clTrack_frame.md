<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTrack_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bank and reference configurations agree

**Claim.** The configuration formed by adjoining the bank of counter configurations to the source tapes and virtual-input buffer equals the corresponding embedded reference configuration.

**Proof.** Compare the configuration fields. The embedded state, input-head position, administrative head positions, and output agree by their definitions. For the work tapes, split the indices into bank tapes and the remaining source and buffer tapes. On a bank index, the bank configuration stores the binary word for the chosen counter; the identity of the counter tape and buffer representations (`Complexity.clCountTape_eq`) makes this exactly the reference configuration's administrative tape. On each remaining index, both constructions retain the virtual-input buffer or the source machine's tape. Thus all work-tape contents agree, and the configurations are equal.

**Key facts.** `Complexity.clCountTape_eq`.
