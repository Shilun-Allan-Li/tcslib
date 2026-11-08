<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_bufferMask -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer Outside the Written Interval

**Claim.** Restricting the buffer for $w$ to the interval $[o,o+|w|)$ leaves its value at $p$ unchanged, since outside that interval the buffer value is blank.

**Proof.** If $p$ lies in the interval, the restriction selects the buffer value, so the equality is immediate. Otherwise, if $p-o$ is nonnegative, being outside the interval implies that its natural-number index is at least $|w|$; list lookup beyond the end of $w$ is none. If $p-o$ is negative, the buffer is none by definition. Thus outside the interval the buffer value is blank, and in either case the restricted expression equals the original buffer value.
