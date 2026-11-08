<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.kCfg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial lifted configuration

**Claim.** The initial configuration of the clock machine on $x$ is the lifted initial configuration of $K$ on $x$.

**Proof.** The initial clock configuration and the lift have the same state, input-head position, and empty output. For the work tapes, split the indices into the block assigned to $K$, the counter tape, and the block assigned to $W$. On the $K$ block, the initial tape contents and head positions agree with those of $K$; the counter tape is blank with its head at the initial output length, which is zero; and every $W$ tape is blank with head at zero. These componentwise equalities establish equality of the configurations.
