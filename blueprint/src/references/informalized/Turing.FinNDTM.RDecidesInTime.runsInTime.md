<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.RDecidesInTime.runsInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting within the time bound

**Claim.** If the one-sided-error decision condition holds, every branch halts within the given time bound on every input.

**Proof.** For each input, the one-sided-error condition directly includes the assertion that every branch of the specified length halts. Taking this first component for each input gives the claimed time bound.
