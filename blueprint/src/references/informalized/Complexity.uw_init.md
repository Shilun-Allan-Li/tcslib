<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial scan configuration

**Claim.** For every Boolean string $x$, the machine’s initial configuration on input $x$ is the scan configuration at position $0$ with an empty buffer.

**Proof.** Unfold the initial configuration and the scan configuration at position $0$. Their states are both the initial state, their input-head positions are both $1$, and their output tapes are both empty. At every work-tape index, both configurations have head position $0$ and an entirely blank tape: the scan tape is blank because its buffer is empty. Thus all configuration fields agree.
