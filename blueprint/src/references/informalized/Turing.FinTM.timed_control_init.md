<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.timed_control_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Controller Configuration

**Claim.** The timed conditional controller's initial configuration on $x$ is its decider-phase configuration corresponding to the decider's initial configuration on $x$.

**Proof.** Compare the configurations field by field. Their states agree because both encode the decider's initial state in the decider phase; their input-head positions and output lists are the same. For each work-tape index in the decider's block, both configurations have the decider's initial blank tape and head at zero. The remaining work tapes also agree: the padding tapes are blank with heads at zero, and the capture tape is blank with its head at the end of the empty captured-output buffer. Thus all configuration fields coincide.
