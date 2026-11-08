<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.sourcePayload_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload at the head positions

**Claim.** At offset zero, the head-centred payload vector equals the vector of symbols read beneath the work-tape heads and the input head, including the input boundary tag.

**Proof.** Equality of the vectors is checked coordinate by coordinate, splitting a virtual coordinate into a work tape or the input tape. On a work tape, offset zero makes the sampled position the head position itself, so the payload is precisely the symbol read there, paired with tag zero. On the input coordinate, the offset-zero input payload is the input symbol at the head together with its boundary tag, by the identification of the input payload at the head position (`inputPayload_head`).

**Key facts.** `Complexity.inputPayload_head`.
