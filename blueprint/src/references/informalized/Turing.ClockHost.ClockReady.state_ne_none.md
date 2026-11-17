<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.ClockReady.state_ne_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting State of a Ready Configuration

**Claim.** Every clock-host configuration that is ready at $m$ has a nonempty state component.

**Proof.** Readiness supplies a simulated configuration $a$ and tape data such that the host configuration is the run-phase configuration built from them. In that construction the state is the run phase carrying $a$'s state and its captured output. A run phase is a constructor distinct from the empty state, so the host state cannot be `none`.
