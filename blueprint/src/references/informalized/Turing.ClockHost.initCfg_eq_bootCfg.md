<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.initCfg_eq_bootCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Host and Boot Configurations

**Claim.** The host machine's initial configuration on $x$ equals the boot configuration formed from the initial configuration of $S$ on $x$.

**Proof.** Configurations are equal once their states, input-head positions, work-tape contents, work-head positions, and output agree. The state, input position, and output agree directly from the definitions of the initial and boot configurations. For work-tape contents, extensionality reduces equality to checking each slot and tape-cell position; for head positions, it reduces equality to checking each slot. The slot classification theorem says every host slot is a yardstick slot, an attempt slot, or the extra slot (`Turing.ClockHost.slots_cases`). In each case, unfolding the initial and boot configurations shows that both sides contain the same initialized tape data and head position. Hence all fields agree.

**Key facts.** `Turing.ClockHost.slots_cases`.
