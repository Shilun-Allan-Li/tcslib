<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p0_turn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Turn to the Second Reset Sweep

**Claim.** From phase $p0$ with the yard head at $-1$, one host step moves the input head left with clamping, advances each of $A$'s work-head positions by one, moves the yard head to $0$, and changes the phase to $p1$, leaving the other listed data and output unchanged.

**Proof.** At yard position $-1$, the yard tape reads no symbol (`yard_neg_one`). The host-step rule identifies the step with the phase transition applied to the configuration (`stepWith_hostCfg`), and the yard-symbol rule identifies the symbol read at the yard head (`hostCfg_symbols_yI`). In phase $p0$, the absence of a mark selects the turn branch, which changes to phase $p1$, moves the input head left, advances the simulated work heads, and moves the yard head right. Applying this action to the host configuration yields the stated result (`apply_hostCfg`).

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.yard_neg_one`, `Turing.ClockHost.hostCfg_symbols_yI`, `Turing.ClockHost.apply_hostCfg`.
