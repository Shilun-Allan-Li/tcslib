<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.sourceWrittenPayload_away -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writes do not affect other offsets

**Claim.** At every nonzero offset, the payload after the origin write prescribed by the totalized machine action equals the configuration’s original head-centred payload.

**Proof.** Compare the two payload vectors coordinate by coordinate, splitting into work tapes and the input tape. On a work tape, the origin-write clause is used only when the offset is zero. Since the given offset is nonzero, both payloads read the same old tape cell and have tag zero. On the input coordinate, the write operation does not alter the fixed input, so both payloads are the same input payload at that offset. Hence the vectors agree.
