<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.apply_hostCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Applying an Action to a Clock-Host Configuration

**Claim.** Applying the assembled action to the host configuration gives the host configuration with the successor phase, moved input head, individually updated tapes and tape heads, and appended output bit.

**Proof.** Compare the two configurations component by component. Their states, input-head positions, and output words agree directly from the definitions of action application and the host configuration. For the work-tape contents, each host tape index belongs to the yardstick group, simulated-tape group, or the single clock-tape position. The index classification (`slots_cases`) reduces the check to these three cases; the slot evaluation facts (`slots_sI`, `slots_aI`, and `slots_yI`) identify the corresponding tape data. In each case, action application performs exactly the tape update recorded by `tapeAfter`. The same three-way classification for head positions shows that each head advances by the movement specified in its instruction. Thus every component agrees.

**Key facts.** `Turing.ClockHost.slots_cases`, `Turing.ClockHost.slots_sI`, `Turing.ClockHost.slots_aI`, `Turing.ClockHost.slots_yI`.
