<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRepeat_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Repetition Configuration

**Claim.** The repetition controller's initial configuration on input $x$, with state word $s$ and unary clock of length $N$, is its start-phase repetition configuration with cursor zero.

**Proof.** Compare configuration fields. The controller's initial state is its start phase, its input-head position is the initial position, and its output is empty, matching the repetition configuration with cursor zero. For the work tapes, split the tape index into the source-tape block and the single clock tape. The source block contains the component words of the state-word encoding, while the last tape contains the unary word of length $N$; both are represented by their buffer contents with heads at zero. These are exactly the work tapes and head positions specified by the start repetition configuration. Thus the configurations agree.
