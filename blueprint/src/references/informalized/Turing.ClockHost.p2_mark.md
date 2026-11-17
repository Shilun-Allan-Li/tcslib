<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p2_mark -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leftward Sweep Mark Step

**Claim.** When the yard tape has a true mark at $z$, one host step in phase $p2$ preserves that phase, advances every work-tape head of $A$ by one, moves the yard head to $z-1$, and leaves the other configuration data unchanged.

**Proof.** The host-step equation reduces the transition to the phase rule, with the yard symbol at its head given by the hypothesis (`stepWith_hostCfg`, `hostCfg_symbols_yI`). Since this symbol is true, the marked-cell branch of phase $p2$ applies: the input movement is zero, the simulated work tapes are not written, every work head of $A$ moves right by one, and the yard head moves left by one. The branch keeps phase $p2$ and emits nothing. The action formula on the host configuration then yields exactly the asserted fields (`apply_hostCfg`).

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.hostCfg_symbols_yI`, `Turing.ClockHost.apply_hostCfg`.
