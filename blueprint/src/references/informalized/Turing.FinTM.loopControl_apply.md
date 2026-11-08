<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopControl_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Controller Action on a Frame

**Claim.** Applying a controller action to the specified frame produces the frame with the prescribed successor state, moved input head, updated flag, counter and payload tapes, moved counter and payload heads, and appended output.

**Proof.** The action sets the successor state and emits the chosen bit, so these become the frame’s state and its old output followed by that bit. Its input-head direction moves the input position according to the machine’s clamped movement rule. The flag tape is distinguished from the counter and payload tapes: its write instruction is applied at the origin, and its head remains at zero. The counter and payload write instructions are applied at their respective current head positions, and their heads move by the chosen directions. Every other tape receives no write and no movement, so it retains the tape and head supplied by the base configuration. These are precisely the components of the stated successor frame.
