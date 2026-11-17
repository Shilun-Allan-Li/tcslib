<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.rew2_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind Step on a Marked Cell

**Claim.** If the yard tape contains a true mark at $z$, one step in phase $rew2$ preserves that phase, moves the input head left by one with boundary clamping, moves the yard head to $z-1$, and leaves the remaining tapes, heads, and output unchanged.

**Proof.** The host-step equation expresses the step as the prescribed phase transition (`stepWith_hostCfg`), and the configuration's yard symbol is its tape value at the yard head (`hostCfg_symbols_yI`). By hypothesis that value is true. The true-mark branch of phase $rew2$ therefore applies: it moves the input head left, leaves all simulated work tapes and their heads idle, moves the yard head left, retains phase $rew2$, and emits nothing. Applying this action to the host configuration gives the claimed fields (`apply_hostCfg`).

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.hostCfg_symbols_yI`, `Turing.ClockHost.apply_hostCfg`.
