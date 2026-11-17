<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p0_mark -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marked Step in the First Reset Sweep

**Claim.** When the yard head in phase $p0$ is on a marked cell, one host step moves the input head left with clamping, advances each of $A$'s work-head positions by one, and moves the yard head left by one, while leaving the phase, tape contents, the $S$ work-head positions, and output unchanged.

**Proof.** The host-step rule for a configuration in a specified phase expresses the step as the phase transition applied to that configuration (`stepWith_hostCfg`). The yard-tape symbol at its head is the tape's value there (`hostCfg_symbols_yI`), which the hypothesis says is true. In phase $p0$, a true symbol selects the marked-cell branch: it prescribes a left input move, no writes, a one-cell advance of each simulated work head, and a left yard-head move. The configuration-application rule translates these action components into the stated resulting configuration (`apply_hostCfg`).

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.hostCfg_symbols_yI`, `Turing.ClockHost.apply_hostCfg`.
