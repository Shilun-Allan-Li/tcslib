<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p1_mark -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marked Step in the Second Reset Sweep

**Claim.** When the yard head in phase $p1$ is on a marked cell, one host step leaves the phase and input head unchanged, advances each of $A$'s work-head positions by one, and moves the yard head right by one, leaving the other tapes and output unchanged.

**Proof.** The host-step rule reduces the transition to applying the action prescribed by the current phase and the symbol read at the yard head (`stepWith_hostCfg`). The yard-symbol rule identifies that read with the tape value at the current yard position (`hostCfg_symbols_yI`), which is true by hypothesis. In phase $p1$, a marked cell selects the branch that keeps the input head fixed, advances each simulated work head and the yard head by one, and writes nothing. The configuration-application rule gives exactly the asserted configuration (`apply_hostCfg`).

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.hostCfg_symbols_yI`, `Turing.ClockHost.apply_hostCfg`.
