<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.run_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clocked Simulation Step

**Claim.** When the yard head is at position $j<m$, one host step from the run configuration encoding $a$ equals the run configuration encoding the result of one step of $A$ from $a$ using choice $b$, with clock position $j+1$.

**Proof.** At position $j<m$, the yard tape contains a true symbol at the head (`yard_of_lt`), so the host transition takes the marked-yard branch of phase $	ext{run}. Split into whether $a$ is already halted. If its state is absent, both the simulated machine and the host preserve the halted configuration (`stepWith_of_halt`); the host nevertheless advances the clock and keeps the captured-output data consistent with the represented configuration. If $a$ has state $q$, the host transition applies the same transition of $A$ using choice $b$: the input symbol and the symbols under $A$'s work-tape heads agree with those read from the represented host configuration. The action-on-host-configurations formula then shows that the input, work tapes, and head positions evolve as in $A$'s step (`apply_hostCfg`). The captured output is also updated correctly, because capturing an output after appending the transition's optional output agrees with pushing that optional bit onto the previous capture (`capOf_append`). In either case the yard head advances by one and the other host data remain in the prescribed representation, establishing the equality.

**Key facts.** `Turing.ClockHost.yard_of_lt`, `Turing.NDTM.stepWith_of_halt`, `Turing.NDTM.stepWith_of_state`, `Turing.ClockHost.hostCfg_symbols_yI`, `Turing.ClockHost.apply_hostCfg`, `Turing.capOf_append`.
