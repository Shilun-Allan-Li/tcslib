<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.rew_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Rewind Step

**Claim.** From phase $	ext{rew}$, one host step moves the input head according to the clamped left move, changes the phase to $	ext{rew2}$, and moves the yard head from $z$ to $z-1$, leaving the other tape contents, head positions, and output unchanged.

**Proof.** The host-step rule expresses the transition from phase $	ext{rew}$ as the action prescribed by the host transition function (`stepWith_hostCfg`). In this phase the action always selects the $	ext{rew2}$ successor, moves the input head left, and moves the yard head left without writing to any tape or producing output. Applying the action to the host configuration therefore gives the clamped left move of the input head and changes the yard-head position from $z$ to $z-1$, while the other tape data and output are preserved (`apply_hostCfg`).

**Key facts.** `Turing.ClockHost.stepWith_hostCfg`, `Turing.ClockHost.apply_hostCfg`.
