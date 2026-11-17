<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCapture_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capture Initialization

**Claim.** The capture machine initialized on $x$ is exactly the embedding of the original machine's initial configuration: it retains the initial state and input-head position, places the empty output buffer with its head at zero, and leaves the remaining added tapes blank with heads at zero.

**Proof.** Both initial configurations have the same state, input-head position, and empty output, so it remains to compare their tape contents and head positions. Split a tape index into the original-tape block, the single buffer tape, and the remaining added tapes. On the original block, the embedded initialization agrees with the original blank tapes and zero head positions; on the buffer tape, the empty output gives an empty buffer and its length is zero; on the remaining tapes, both contents are blank and heads are at zero. Thus every configuration field agrees.
