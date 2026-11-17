<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.inputPayload_outside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Payloads Outside the Input

**Claim.** If an integer coordinate lies strictly to the left of $-1$ or strictly to the right of the input length, its virtual input payload is blank.

**Proof.** Split into the two alternatives. If $z<-1$, then $z$ is negative, so the buffer tape returns no symbol; also $z$ is neither boundary coordinate $-1$ nor $|x|$. If $|x|<z$, then $z$ is nonnegative, is again neither boundary coordinate, and its natural-number index is at least $|x|$, so the list lookup is absent. In both cases the symbol component is `none` and the tag is $0$, which is the blank payload.
