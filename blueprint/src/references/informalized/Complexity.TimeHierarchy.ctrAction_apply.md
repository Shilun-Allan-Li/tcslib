<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Action on Configurations

**Claim.** Applying a counter action updates the clock state, buffer tape, and buffer head as specified, leaving the simulated configuration, the $K$ work tapes, and output unchanged.

**Proof.** Compare the configuration components. The input-head movement in the counter action is zero, so the input position is unchanged (`moveInputPos_zero`). The block decomposition of work tapes and head positions divides them into the $K$ tapes, the distinguished buffer tape, and the $W$ tapes. On the outer blocks, the counter action makes no writes and no head movements. On the distinguished buffer tape, an absent write leaves the tape function unchanged, while a present write updates it at the old head position; the head then moves by $d$. The action sets the state to $q$ and emits no output. These componentwise equalities give the stated configuration.

**Key facts.** `Turing.moveInputPos_zero`.
