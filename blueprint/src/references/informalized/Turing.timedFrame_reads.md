<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedFrame_reads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reads in the Framed Configuration

**Claim.** The six symbols read on the framed configuration’s four core tapes, clock tape, and buffer tape, in that order, are exactly the six symbols read from the original configuration.

**Proof.** Evaluate the equality at each of the six tape indices. For the first four indices, the framed configuration selects the corresponding core tape, whose contents and head position come directly from the original configuration. At the fifth index it selects the clock tape, and at the sixth it selects the buffer tape; in both cases the contents and head position again agree with those of the corresponding original tape. Thus each of the six read symbols agrees, giving equality of the tuples.
