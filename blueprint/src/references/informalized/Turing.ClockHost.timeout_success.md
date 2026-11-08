<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.timeout_success -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successful timeout step

**Claim.** If the encoded nondeterministic configuration is halted with output $[v]$, then the host's timeout step halts, outputs $[v]$, and preserves the input position, work tapes and head positions, and yardstick with its head at $m$.

**Proof.** The run configuration records the halted state and captures its singleton output as the single Boolean symbol $v$. At clock position $m$, the yardstick is blank, so the transition uses the blank-clock branch of the run phase. Because the captured state is halted and the captured output is a single symbol, this branch emits $v$ and halts. Applying that action leaves the input and work-tape data unchanged and keeps the clock head at $m$; the yardstick remains the same. The output, previously empty in the run configuration, becomes the singleton word $[v]$.

**Key facts.** `Turing.NDTM.stepWith_of_state`, `Turing.ClockHost.hostCfg_symbols_yI`, `Turing.ClockHost.yard_len`, `Turing.ClockHost.apply_hostCfg`.
